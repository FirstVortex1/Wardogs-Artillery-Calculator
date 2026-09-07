"""Vortex's Artillery & AOE Dispersion Calculator.

Utility software for wardogs setup to make artillery much easier
I've done a lot of work to make this program secure however it still
reads from github so I can update defualt locations without having to
redistribue data.

If you would like to disable this system go to line 64 and remove 
the URL from the variable. It will look for default_locations.xml
in the same folder as itself so feel free to download manually or
just ignore it and the whole feature will stay disabled
"""

import math
import os
import re
import sys
import tkinter as tk
from tkinter import messagebox, simpledialog
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
import xml.parsers.expat
from typing import List, Optional, Set, Tuple

# --- COLOR PALETTE & STYLING CONSTANTS ---
BG_COLOR = "#181a22"  # Main window background
CARD_BG = "#222531"  # Section card background
FIELD_BG = "#13141c"  # Input box background
BORDER_COLOR = "#333748"  # Subtle border stroke
TEXT_LIGHT = "#e1e4ee"  # Primary label / text color
TEXT_MUTED = "#8289a0"  # Secondary / field label text
ACCENT_BLUE = "#7a8ff6"  # Header text accent
ACCENT_CYAN = "#00d2ff"  # Dispersion section header
CYAN_BORDER = "#0096c7"  # Dispersion box border stroke

BTN_GRAY = "#404452"  # Neutral dark button
BTN_RED = "#c52828"  # Reset / danger button
BTN_GREEN = "#2e7d32"  # Confirm hit / Active status button

# Hover ("active") shades for each button color above, keyed by base color so
# any button factory call can look up its own hover state automatically.
BTN_HOVER = {
    BTN_GRAY: "#4f5466",
    BTN_GREEN: "#3b963e",
    BTN_RED: "#db3232",
}

RANGE_IN = "#4ade80"  # Bright green for in-range artillery
RANGE_OUT = "#ef4444"  # Red for out-of-range artillery

FONT_TITLE = ("Segoe UI", 12, "bold")
FONT_SECTION = ("Segoe UI", 10, "bold")
FONT_LABEL = ("Segoe UI", 9)
FONT_VALUE_LARGE = ("Segoe UI", 14, "bold")
FONT_INDICATOR = ("Segoe UI", 8, "bold")
FONT_BUTTON = ("Segoe UI", 9, "bold")
FONT_BUTTON_SMALL = ("Segoe UI", 8, "bold")
FONT_ENTRY = ("Segoe UI", 10)
FONT_LISTBOX = ("Consolas", 9)

# Resolve path and remote URL configuration for default locations
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
XML_URL = "https://raw.githubusercontent.com/FirstVortex1/Wardogs-Artillery-Calculator/5f22a057b6b958c573072b8716e963a0d89b2481/default_locations.xml"
XML_LOCAL_FALLBACK = os.path.join(SCRIPT_DIR, "default_locations.xml")

# --- SECURITY: REMOTE XML HARDENING ---
# The location list is fetched from a GitHub account. If that account were ever
# compromised, an attacker's only lever is "whatever bytes come back from that URL",
# so everything below treats the downloaded XML as fully untrusted input: it is size
# limited, parsed with entity/DTD expansion disabled (XXE / billion-laughs protection),
# and every field is type-checked, bounds-checked, and whitelisted before use.
ALLOWED_XML_HOSTS = {"raw.githubusercontent.com"}
MAX_XML_DOWNLOAD_BYTES = 10 * 1024 * 1024  # 10 MB hard cap on the XML payload
MAX_LOCATION_ENTRIES = 5000  # sane upper bound on how many <location> rows we trust
MAX_STRING_FIELD_LEN = 80  # max length for map/location name text fields
COORD_MIN_VALUE, COORD_MAX_VALUE = -100000.0, 100000.0  # sane in-game coordinate bounds
_SAFE_TEXT_PATTERN = re.compile(r"^[A-Za-z0-9 _\-\.\,'\(\)#/]+$")


class XMLSecurityError(Exception):
    """Raised when incoming XML fails a security/sanity check and must not be trusted."""


def _reject_doctype(*_args, **_kwargs) -> None:
    raise XMLSecurityError("DOCTYPE declarations are not permitted in location data.")


def _reject_entity_decl(*_args, **_kwargs) -> None:
    raise XMLSecurityError("Custom XML entities are not permitted in location data.")


def _reject_external_entity(*_args, **_kwargs) -> int:
    # A falsy return tells expat to abort the parse instead of resolving the reference,
    # which is what closes off classic XXE (file/network read via external entities).
    return 0


def secure_xml_fromstring(data: bytes) -> ET.Element:
    """Parses XML bytes with entity expansion and DOCTYPEs disabled.

    This is a defusedxml-style hardened parse built directly on the public
    xml.parsers.expat API (no extra dependency, and no reliance on private
    ElementTree internals that vary between the C-accelerated and pure-Python
    builds) so a malicious or corrupted XML payload can't be used for XXE,
    billion-laughs style entity expansion, or unbounded-size denial of service.
    """
    if not isinstance(data, (bytes, bytearray)):
        raise TypeError("XML source data must be raw bytes.")

    if len(data) == 0:
        raise XMLSecurityError("Received an empty XML payload.")

    if len(data) > MAX_XML_DOWNLOAD_BYTES:
        raise XMLSecurityError(
            f"XML payload of {len(data)} bytes exceeds the "
            f"{MAX_XML_DOWNLOAD_BYTES}-byte limit."
        )

    # Cheap, human-readable fail-fast before the payload even reaches the parser.
    header = bytes(data[:4096]).lower()
    if b"<!doctype" in header or b"<!entity" in header:
        raise XMLSecurityError(
            "DOCTYPE/ENTITY declarations are not permitted in location data."
        )

    builder = ET.TreeBuilder()
    expat_parser = xml.parsers.expat.ParserCreate()
    expat_parser.buffer_text = True

    expat_parser.StartElementHandler = lambda name, attrs: builder.start(name, attrs)
    expat_parser.EndElementHandler = builder.end
    expat_parser.CharacterDataHandler = builder.data

    # Belt-and-suspenders on top of the header pre-check: even if a DOCTYPE/entity
    # declaration slipped past it (e.g. odd whitespace/casing), these handlers make
    # expat itself refuse to process it.
    expat_parser.StartDoctypeDeclHandler = _reject_doctype
    expat_parser.EntityDeclHandler = _reject_entity_decl
    expat_parser.UnparsedEntityDeclHandler = _reject_entity_decl
    expat_parser.ExternalEntityRefHandler = _reject_external_entity

    try:
        expat_parser.Parse(bytes(data), True)
    except XMLSecurityError:
        raise
    except xml.parsers.expat.ExpatError as e:
        raise XMLSecurityError(f"Malformed XML: {e}") from e

    return builder.close()


def _sanitize_text_field(raw_value: object, *, default: str) -> str:
    """Validates/coerces an attribute into a short, printable, whitelisted string.

    Anything that isn't a plain string, is empty, or contains characters outside the
    allow-list (e.g. markup, control characters, path/command-injection punctuation)
    falls back to `default` rather than being trusted verbatim.
    """
    if not isinstance(raw_value, str):
        return default
    value = "".join(ch for ch in raw_value.strip() if ch.isprintable())
    if not value:
        return default
    value = value[:MAX_STRING_FIELD_LEN]
    if not _SAFE_TEXT_PATTERN.match(value):
        return default
    return value


def _sanitize_coordinate(raw_value: object) -> Optional[str]:
    """Validates a coordinate attribute is a finite, in-range number.

    Returns a clean canonical string form on success, or None if the value should
    be treated as unusable (missing, non-numeric, NaN/inf, or out of bounds) so the
    caller can drop the entry instead of crashing or plotting garbage coordinates.
    """
    if raw_value is None:
        return None
    if isinstance(raw_value, bool):
        return None
    try:
        num = float(str(raw_value).strip())
    except (TypeError, ValueError):
        return None
    if not math.isfinite(num):
        return None
    if not (COORD_MIN_VALUE <= num <= COORD_MAX_VALUE):
        return None
    return f"{num:g}"


def _extract_locations_from_root(root: ET.Element) -> Tuple[List[dict], Set[str]]:
    """Walks a parsed <locations> tree, validating/sanitizing every attribute.

    Malformed individual entries (bad coordinates, wrong types, etc.) are silently
    skipped rather than trusted or allowed to crash the whole load.
    """
    locations: List[dict] = []
    maps_set: Set[str] = set()

    if root is None:
        return locations, maps_set

    for elem in root.findall("location"):
        if len(locations) >= MAX_LOCATION_ENTRIES:
            break
        if not isinstance(elem.tag, str):
            continue  # skip comments/processing-instructions, which aren't real rows

        m_name = _sanitize_text_field(elem.get("map"), default="Unknown Map")
        l_name = _sanitize_text_field(elem.get("name"), default="Unnamed")
        x_val = _sanitize_coordinate(elem.get("x"))
        y_val = _sanitize_coordinate(elem.get("y"))

        if x_val is None or y_val is None:
            continue  # unusable coordinates - drop the entry rather than guess

        locations.append({"map": m_name, "name": l_name, "x": x_val, "y": y_val})
        maps_set.add(m_name)

    return locations, maps_set


# --- WINDOWS CONSOLE MANAGEMENT ---
if sys.platform.startswith("win"):
    import ctypes

    _console_window = ctypes.windll.kernel32.GetConsoleWindow()
    if _console_window != 0:
        ctypes.windll.user32.ShowWindow(_console_window, 0)


def parse_coords_string(coord_str: str) -> Tuple[Optional[str], Optional[str]]:
    """Extracts the first two numerical coordinate values from a raw input string."""
    numbers = re.findall(r"[-+]?\d*\.\d+|\d+", coord_str)
    if len(numbers) >= 2:
        return numbers[0], numbers[1]
    return None, None


class BallisticsEngine:
    """Pure mathematical helper methods for ballistics and dispersion spread."""

    @staticmethod
    def calculate_solution(
        gun_x: float,
        gun_y: float,
        target_x: float,
        target_y: float,
        aoe_diameter: float,
    ) -> dict:
        """Calculates distance, bearing, and AOE dispersion boundaries."""
        gx, gy = gun_x * 100.0, gun_y * 100.0
        tx, ty = target_x * 100.0, target_y * 100.0

        dx = tx - gx
        dy = ty - gy

        distance = math.hypot(dx, dy)
        bearing = (math.degrees(math.atan2(dx, dy)) + 360) % 360

        radius = aoe_diameter / 2.0
        area = math.pi * (radius**2)

        min_dist = max(0.0, distance - radius)
        max_dist = distance + radius

        delta_bearing = (
            math.degrees(math.atan2(radius, distance)) if distance > 0 else 0.0
        )
        min_bear = (bearing - delta_bearing + 360) % 360
        max_bear = (bearing + delta_bearing + 360) % 360

        return {
            "bearing": bearing,
            "distance": distance,
            "min_bearing": min_bear,
            "max_bearing": max_bear,
            "delta_bearing": delta_bearing,
            "min_distance": min_dist,
            "max_distance": max_dist,
            "radius": radius,
            "area": area,
        }


class VortexArtyCalculator:
    """Main Application Window for the Artillery Calculator."""

    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title("Vortex's Fancy Vibe Coded Artillery Calculator")
        self.root.geometry("1160x720")
        self.root.configure(bg=BG_COLOR)
        self.root.resizable(False, False)

        # --- STATE VARIABLES ---
        self.gun_x = tk.StringVar(value="")
        self.gun_y = tk.StringVar(value="")

        self.target_x = tk.StringVar(value="")
        self.target_y = tk.StringVar(value="")

        self.impact_x = tk.StringVar(value="")
        self.impact_y = tk.StringVar(value="")

        self.aoe_dist = tk.StringVar(value="30")

        # Quick Paste StringVars
        self.gun_paste = tk.StringVar()
        self.target_paste = tk.StringVar()
        self.impact_paste = tk.StringVar()

        # Clipboard Watcher State
        self.is_watching_clipboard = False
        self.last_clipboard_text = ""

        # Accumulated Miss Offsets (In-Game Units)
        self.offset_x = 0.0
        self.offset_y = 0.0

        # Shot Miss Log Tracking
        self.miss_history = []
        self.shot_counter = 0
        self.is_miss_log_visible = False
        self.last_applied_impact = None  # (imp_x, imp_y) of the last shot folded into offset_x/offset_y

        # Saved Solutions Storage & Counter
        self.saved_solutions = []
        self.solution_counter = 1
        self.solution_name_var = tk.StringVar(value="Solution 1")

        # Current Live Output (for saving)
        self.current_bearing = None
        self.current_distance = None

        # XML Default Locations Storage
        self.xml_locations = []
        self.available_maps = []
        self.selected_map_var = tk.StringVar(value="")
        self.has_xml = False
        self.load_xml_locations()

        # --- UI INITIALIZATION & BINDINGS ---
        self._build_ui()
        self._register_traces()
        self.update_live_solution()

    # --- XML LOADING FROM REMOTE URL / FALLBACK ---

    def load_xml_locations(self) -> None:
        """Parses default locations and available maps from the remote XML URL or local
        fallback. All XML is treated as untrusted: the remote host is allow-listed, the
        payload is size-capped, parsed with a hardened XXE/DTD-safe parser, and every
        field is type/bounds-checked before it reaches the rest of the app."""
        self.xml_locations.clear()
        maps_set: Set[str] = set()
        success = False

        # Only fetch from the expected host - if XML_URL was ever changed to point
        # somewhere unexpected (e.g. tampered config), refuse the remote fetch outright.
        remote_host = urllib.parse.urlparse(XML_URL).hostname
        remote_is_allowed = remote_host in ALLOWED_XML_HOSTS

        if remote_is_allowed:
            try:
                request = urllib.request.Request(
                    XML_URL, headers={"User-Agent": "VortexArtyCalculator/1.0"}
                )
                with urllib.request.urlopen(request, timeout=5) as response:
                    # Read one byte past the cap so an oversized payload is detected
                    # without ever buffering an unbounded amount of attacker-controlled data.
                    xml_data = response.read(MAX_XML_DOWNLOAD_BYTES + 1)
                if len(xml_data) > MAX_XML_DOWNLOAD_BYTES:
                    raise XMLSecurityError("Remote XML exceeded the maximum allowed size.")

                root = secure_xml_fromstring(xml_data)
                self.xml_locations, maps_set = _extract_locations_from_root(root)
                success = True
            except Exception:
                # Any network, security, or parsing failure falls through to the local
                # fallback below rather than trusting a half-parsed remote payload.
                success = False

        # Fallback to local file if the remote host was rejected, unreachable, or unsafe
        if not success and os.path.exists(XML_LOCAL_FALLBACK):
            try:
                with open(XML_LOCAL_FALLBACK, "rb") as f:
                    local_data = f.read(MAX_XML_DOWNLOAD_BYTES + 1)
                if len(local_data) > MAX_XML_DOWNLOAD_BYTES:
                    raise XMLSecurityError(
                        "Local fallback XML exceeded the maximum allowed size."
                    )

                root = secure_xml_fromstring(local_data)
                self.xml_locations, maps_set = _extract_locations_from_root(root)
                success = True
            except XMLSecurityError as e:
                messagebox.showerror(
                    "XML Security Error", f"Local fallback XML failed a security check:\n{e}"
                )
            except Exception as e:
                messagebox.showerror(
                    "XML Error", f"Failed to parse local fallback XML:\n{e}"
                )

        self.has_xml = success
        self.available_maps = sorted(maps_set)
        if self.available_maps and self.selected_map_var.get() not in self.available_maps:
            self.selected_map_var.set(self.available_maps[0])

    # --- STYLE HELPERS (WIDGET FACTORIES) ---

    def _make_card(
        self,
        parent: tk.Widget,
        *,
        bg: str = CARD_BG,
        border: str = BORDER_COLOR,
        width: Optional[int] = None,
    ) -> tk.Frame:
        """Bordered 'card' container frame used for sidebars and section boxes."""
        kwargs = dict(
            bg=bg, bd=1, relief="solid", highlightbackground=border, highlightthickness=1
        )
        if width is not None:
            kwargs["width"] = width
        return tk.Frame(parent, **kwargs)

    def _make_divider(self, parent: tk.Widget, *, bg: str = BORDER_COLOR) -> tk.Frame:
        """Thin horizontal rule used to separate a card's header from its body."""
        return tk.Frame(parent, bg=bg, height=1)

    def _make_section_label(
        self,
        parent: tk.Widget,
        text: str,
        *,
        fg: str = TEXT_LIGHT,
        bg: str = CARD_BG,
        font=FONT_SECTION,
    ) -> tk.Label:
        """Bold header-style label (section titles, card headers)."""
        return tk.Label(parent, text=text, font=font, fg=fg, bg=bg, anchor="w")

    def _make_field_label(self, parent: tk.Widget, text: str, *, bg: str = CARD_BG) -> tk.Label:
        """Small muted label placed above an input field."""
        return tk.Label(parent, text=text, font=FONT_LABEL, fg=TEXT_MUTED, bg=bg, anchor="w")

    def _make_value_label(self, parent: tk.Widget, text: str, *, bg: str = "#12131a") -> tk.Label:
        """Large bold readout value (e.g. bearing/distance)."""
        return tk.Label(parent, text=text, font=FONT_VALUE_LARGE, fg=TEXT_LIGHT, bg=bg)

    def _make_indicator_label(self, parent: tk.Widget, text: str) -> tk.Label:
        """Small range-status indicator label (e.g. 'SPH-2', 'Mortar')."""
        return tk.Label(parent, text=text, font=FONT_INDICATOR, fg=TEXT_MUTED, bg=CARD_BG)

    def _make_entry(
        self, parent: tk.Widget, text_var: tk.StringVar, *, with_highlight: bool = True
    ) -> tk.Entry:
        """Styled text entry bound to a StringVar."""
        kwargs = dict(
            textvariable=text_var,
            font=FONT_ENTRY,
            fg=TEXT_LIGHT,
            bg=FIELD_BG,
            insertbackground=TEXT_LIGHT,
            bd=1,
            relief="solid",
        )
        if with_highlight:
            kwargs["highlightbackground"] = BORDER_COLOR
            kwargs["highlightthickness"] = 1
        return tk.Entry(parent, **kwargs)

    def _make_button(
        self,
        parent: tk.Widget,
        text: str,
        bg: str,
        command,
        *,
        font=FONT_BUTTON,
        height: Optional[int] = None,
    ) -> tk.Button:
        """Styled flat button; its hover color is looked up from BTN_HOVER."""
        kwargs = dict(
            text=text,
            font=font,
            fg=TEXT_LIGHT,
            bg=bg,
            activebackground=BTN_HOVER.get(bg, bg),
            activeforeground=TEXT_LIGHT,
            bd=0,
            cursor="hand2",
            command=command,
        )
        if height is not None:
            kwargs["height"] = height
        return tk.Button(parent, **kwargs)

    def _make_scrollbar(self, parent: tk.Widget) -> tk.Scrollbar:
        """Vertical scrollbar, packed to the right edge of its parent."""
        scrollbar = tk.Scrollbar(parent, orient="vertical")
        scrollbar.pack(side="right", fill="y")
        return scrollbar

    def _make_listbox(
        self, parent: tk.Widget, *, yscrollcommand, height: Optional[int] = None
    ) -> tk.Listbox:
        """Styled listbox wired up to a scrollbar's yscrollcommand."""
        kwargs = dict(
            font=FONT_LISTBOX,
            fg=TEXT_LIGHT,
            bg=FIELD_BG,
            selectbackground=BTN_GRAY,
            selectforeground=TEXT_LIGHT,
            bd=1,
            relief="solid",
            highlightcolor=BORDER_COLOR,
            yscrollcommand=yscrollcommand,
        )
        if height is not None:
            kwargs["height"] = height
        return tk.Listbox(parent, **kwargs)

    # --- UI BUILDING METHODS ---

    def _build_ui(self) -> None:
        """Constructs the complete application UI layout with conditional sidebars."""
        # Main Title Header
        tk.Label(
            self.root,
            text="VORTEX'S FANCY VIBE CODED ARTILLERY CALCULATOR",
            font=FONT_TITLE,
            fg=ACCENT_BLUE,
            bg=BG_COLOR,
        ).pack(pady=(8, 4))

        # Main Workspace Container
        self.main_container = tk.Frame(self.root, bg=BG_COLOR)
        self.main_container.pack(fill="both", expand=True, padx=8, pady=(0, 8))

        # Left Sidebar: Miss Error Log & Impact Visualizer (Closed by default)
        self.miss_frame = self._make_card(self.main_container, width=240)
        self.miss_frame.pack_propagate(False)
        self._build_miss_log_sidebar(self.miss_frame)

        # Center Column: Calculator Inputs & Output
        self.left_frame = tk.Frame(self.main_container, bg=BG_COLOR)
        self.left_frame.pack(side="left", fill="both", expand=True)

        # Right Container for Sidebars
        right_container = tk.Frame(self.main_container, bg=BG_COLOR)
        right_container.pack(side="right", fill="both", padx=(6, 0))

        # Right Sidebar 1: Saved Bearings Sidebar
        self.right_frame = self._make_card(right_container, width=280)
        self.right_frame.pack(
            side="left", fill="both", padx=(0, 4) if self.has_xml else 0
        )
        self.right_frame.pack_propagate(False)

        # Right Sidebar 2: Default Locations Sidebar (Only packed if XML is successfully loaded)
        if self.has_xml:
            self.default_frame = self._make_card(right_container, width=280)
            self.default_frame.pack(side="right", fill="both")
            self.default_frame.pack_propagate(False)

        # Section Cards on the Left/Center Frame
        self._build_setup_card(self.left_frame)
        self._build_readout_card(self.left_frame)
        self._build_spotter_card(self.left_frame)

        # Build Sidebars
        self._build_sidebar(self.right_frame)
        if self.has_xml:
            self._build_default_sidebar(self.default_frame)

    def _build_miss_log_sidebar(self, parent: tk.Widget) -> None:
        """Constructs the left sidebar table for logging shot error distances and the visual impact plotter."""
        header_frame = tk.Frame(parent, bg=CARD_BG)
        header_frame.pack(fill="x", padx=10, pady=(8, 4))

        self._make_section_label(
            header_frame, "🎯 SHOT ERROR LOG", fg=ACCENT_CYAN
        ).pack(side="left")

        self._make_divider(parent).pack(fill="x", padx=10, pady=(0, 6))

        # Table Column Header
        tbl_header = tk.Frame(parent, bg=FIELD_BG)
        tbl_header.pack(fill="x", padx=8, pady=(0, 2))

        tk.Label(
            tbl_header,
            text="Shot #",
            font=("Consolas", 9, "bold"),
            fg=ACCENT_CYAN,
            bg=FIELD_BG,
            width=8,
            anchor="w",
        ).pack(side="left", padx=(4, 0), pady=2)

        tk.Label(
            tbl_header,
            text="Error Dist (m)",
            font=("Consolas", 9, "bold"),
            fg=ACCENT_CYAN,
            bg=FIELD_BG,
            anchor="e",
        ).pack(side="right", padx=(0, 4), pady=2)

        # Scrollable Miss Table Listbox
        list_frame = tk.Frame(parent, bg=CARD_BG)
        list_frame.pack(fill="x", padx=8, pady=(0, 4))

        scrollbar = self._make_scrollbar(list_frame)
        self.listbox_misses = self._make_listbox(
            list_frame, yscrollcommand=scrollbar.set, height=7
        )
        self.listbox_misses.pack(side="left", fill="both", expand=True)
        scrollbar.config(command=self.listbox_misses.yview)

        # Section Header: Visual Plotter
        vis_header = tk.Frame(parent, bg=CARD_BG)
        vis_header.pack(fill="x", padx=10, pady=(6, 2))

        self._make_section_label(
            vis_header, "📍 IMPACT PLOTTER (TO SCALE)", fg=ACCENT_CYAN
        ).pack(side="left")

        self._make_divider(parent).pack(fill="x", padx=10, pady=(0, 6))

        # Canvas Widget for Visual Representation
        canvas_frame = tk.Frame(parent, bg=CARD_BG)
        canvas_frame.pack(fill="both", expand=True, padx=8, pady=(0, 8))

        self.canvas_vis = tk.Canvas(
            canvas_frame,
            bg=FIELD_BG,
            bd=1,
            relief="solid",
            highlightbackground=BORDER_COLOR,
            highlightthickness=1,
            height=230,
        )
        self.canvas_vis.pack(fill="both", expand=True)
        self.canvas_vis.bind("<Configure>", lambda e: self.update_impact_visualizer())

    def show_miss_log(self) -> None:
        """Opens and displays the left miss log sidebar."""
        if not self.is_miss_log_visible:
            self.miss_frame.pack(
                side="left", fill="both", padx=(0, 6), before=self.left_frame
            )
            self.is_miss_log_visible = True
            self.root.geometry("1400x720")

    def hide_miss_log(self) -> None:
        """Hides and closes the left miss log sidebar."""
        if self.is_miss_log_visible:
            self.miss_frame.pack_forget()
            self.is_miss_log_visible = False
            self.root.geometry("1160x720")

    def clear_miss_log(self) -> None:
        """Clears all records in the miss log table and visual history."""
        self.listbox_misses.delete(0, tk.END)
        self.miss_history.clear()
        self.shot_counter = 0

    def _build_setup_card(self, parent: tk.Widget) -> None:
        """Builds Section 1: Setup & Target Parameters with artillery range indicators."""
        card = self._make_card(parent)
        card.pack(fill="both", expand=True, pady=(0, 4))

        header_frame = tk.Frame(card, bg=CARD_BG)
        header_frame.pack(fill="x", padx=10, pady=(4, 2))

        self._make_section_label(header_frame, "1. Setup & Target Parameters").pack(
            side="left"
        )

        indicators_frame = tk.Frame(header_frame, bg=CARD_BG)
        indicators_frame.pack(side="right")

        self.lbl_sph2_indicator = self._make_indicator_label(indicators_frame, "SPH-2")
        self.lbl_sph2_indicator.pack(side="right", padx=(8, 0))

        self.lbl_mortar_indicator = self._make_indicator_label(indicators_frame, "Mortar")
        self.lbl_mortar_indicator.pack(side="right", padx=(8, 0))

        self._make_divider(card).pack(fill="x", padx=10, pady=(0, 4))

        grid = tk.Frame(card, bg=CARD_BG)
        grid.pack(fill="x", padx=6, pady=(0, 6))
        for col in range(3):
            grid.columnconfigure(col, weight=1)

        self._create_quick_paste_field(
            grid, "Quick Paste Gunner", self.gun_paste, row=0, col=0
        )
        self._create_field(grid, "Gunner X", self.gun_x, row=1, col=0)
        self._create_field(grid, "Gunner Y", self.gun_y, row=2, col=0)

        self._create_quick_paste_field(
            grid, "Quick Paste Target", self.target_paste, row=0, col=1
        )
        self._create_field(grid, "Target X", self.target_x, row=1, col=1)
        self._create_field(grid, "Target Y", self.target_y, row=2, col=1)

        self._create_field(
            grid, "Desired AOE Diameter (m)", self.aoe_dist, row=0, col=2, placeholder="30"
        )

        f_watch = tk.Frame(grid, bg=CARD_BG)
        f_watch.grid(row=1, column=2, sticky="ew", padx=4, pady=2)

        self._make_field_label(f_watch, "Clipboard Monitor").pack(
            fill="x", anchor="w", pady=(0, 1)
        )

        self.btn_auto_clip = self._make_button(
            f_watch, "📡 Auto-Target: OFF", BTN_GRAY, self.toggle_clipboard_watch
        )
        self.btn_auto_clip.pack(fill="x", ipady=2)

        f_reset = tk.Frame(grid, bg=CARD_BG)
        f_reset.grid(row=2, column=2, sticky="ew", padx=4, pady=2)

        self._make_field_label(f_reset, "Reset").pack(fill="x", anchor="w", pady=(0, 1))

        self._make_button(
            f_reset, "🔄 Clear All Fields", BTN_RED, self.clear_all_inputs,
            font=FONT_BUTTON_SMALL,
        ).pack(fill="x", ipady=2)

    def _build_readout_card(self, parent: tk.Widget) -> None:
        """Builds the primary firing solution and AOE dispersion readout card."""
        card = self._make_card(parent, bg="#12131a", border="#2f3448")
        card.pack(fill="both", expand=True, pady=4)

        readout_header = tk.Frame(card, bg="#12131a")
        readout_header.pack(fill="x", padx=10, pady=(4, 2))

        self._make_field_label(readout_header, "CURRENT FIRING DATA", bg="#12131a").pack(
            side="left"
        )

        readout_content = tk.Frame(card, bg="#12131a")
        readout_content.pack(fill="x", padx=10, pady=(0, 4))

        self.lbl_bearing = self._make_value_label(readout_content, "Bearing: ---°")
        self.lbl_bearing.pack(side="left")

        self.lbl_distance = self._make_value_label(readout_content, "Distance: --- m")
        self.lbl_distance.pack(side="right")

        disp_box = self._make_card(card, bg="#0f1118", border=CYAN_BORDER)
        disp_box.pack(fill="x", padx=8, pady=(4, 6))

        self._make_section_label(
            disp_box, "AOE BARRAGE DISPERSION SPREAD", fg=ACCENT_CYAN, bg="#0f1118"
        ).pack(fill="x", padx=10, pady=(6, 4))

        stats_grid = tk.Frame(disp_box, bg="#0f1118")
        stats_grid.pack(fill="x", padx=10, pady=(0, 6))
        stats_grid.columnconfigure(0, weight=1)
        stats_grid.columnconfigure(1, weight=1)

        self.lbl_disp_bearing = self._add_stat_row(
            stats_grid, "Bearing Spread:", row=0
        )
        self.lbl_disp_distance = self._add_stat_row(
            stats_grid, "Distance Spread:", row=1
        )
        self.lbl_disp_area = self._add_stat_row(
            stats_grid, "Target Area Coverage:", row=2
        )

    def _build_spotter_card(self, parent: tk.Widget) -> None:
        """Builds Section 2: Spotter & Miss Correction inputs and control buttons."""
        card = self._make_card(parent)
        card.pack(fill="both", expand=True, pady=(4, 4))

        self._make_section_label(card, "2. Spotter & Miss Correction").pack(
            fill="x", padx=10, pady=(4, 2)
        )

        self._make_divider(card).pack(fill="x", padx=10, pady=(0, 4))

        grid = tk.Frame(card, bg=CARD_BG)
        grid.pack(fill="x", padx=6)
        grid.columnconfigure(0, weight=1)
        grid.columnconfigure(1, weight=1)

        self._create_quick_paste_field(
            grid, "Quick Paste Impact", self.impact_paste, row=0, col=0, columnspan=2
        )
        self._create_field(grid, "Impact X", self.impact_x, row=1, col=0)
        self._create_field(grid, "Impact Y", self.impact_y, row=1, col=1)

        btn_frame = tk.Frame(card, bg=CARD_BG)
        btn_frame.pack(fill="x", padx=10, pady=6)

        self._make_button(
            btn_frame, "⚠️ Confirm Miss (Chain Correction)", BTN_GRAY,
            self.apply_miss_correction, height=2,
        ).pack(fill="x", pady=(0, 4))

        row_btns = tk.Frame(btn_frame, bg=CARD_BG)
        row_btns.pack(fill="x")

        self._make_button(
            row_btns, "🎯 Confirm Hit (Set Target)", BTN_GREEN, self.confirm_hit, height=2,
        ).pack(side="left", fill="x", expand=True, padx=(0, 3))

        self._make_button(
            row_btns, "Reset Corrections", BTN_RED, self.reset_corrections, height=2,
        ).pack(side="right", fill="x", expand=True, padx=(3, 0))

    def _on_listbox_click(self, event, listbox: tk.Listbox) -> Optional[str]:
        """Prevents selection when clicking in the empty space below the last listbox item."""
        index = listbox.nearest(event.y)
        if index >= 0:
            bbox = listbox.bbox(index)
            if bbox:
                item_y = bbox[1]
                item_height = bbox[3]
                if event.y > (item_y + item_height):
                    listbox.selection_clear(0, tk.END)
                    return "break"
        return None

    def _build_sidebar(self, parent: tk.Widget) -> None:
        """Constructs the right sidebar for saved solutions."""
        self._make_section_label(parent, "📌 SAVED SOLUTIONS", fg=ACCENT_CYAN).pack(
            fill="x", padx=10, pady=(8, 4)
        )

        self._make_divider(parent).pack(fill="x", padx=10, pady=(0, 6))

        name_frame = tk.Frame(parent, bg=CARD_BG)
        name_frame.pack(fill="x", padx=10, pady=(0, 6))

        self._make_field_label(name_frame, "Solution Name").pack(fill="x", pady=(0, 1))

        entry_name = self._make_entry(name_frame, self.solution_name_var)
        entry_name.pack(fill="x", ipady=2)

        self._make_button(
            parent, "💾 Save Current Solution", BTN_GRAY, self.save_current_solution,
        ).pack(fill="x", padx=10, pady=(0, 6), ipady=3)

        list_frame = tk.Frame(parent, bg=CARD_BG)
        list_frame.pack(fill="both", expand=True, padx=8, pady=(0, 6))

        scrollbar = self._make_scrollbar(list_frame)
        self.listbox_saved = self._make_listbox(list_frame, yscrollcommand=scrollbar.set)
        self.listbox_saved.pack(side="left", fill="both", expand=True)
        scrollbar.config(command=self.listbox_saved.yview)

        self.listbox_saved.bind(
            "<Button-1>", lambda e: self._on_listbox_click(e, self.listbox_saved)
        )
        self.listbox_saved.bind(
            "<Double-Button-1>", lambda e: self.load_selected_solution()
        )

        btn_box = tk.Frame(parent, bg=CARD_BG)
        btn_box.pack(fill="x", padx=8, pady=(0, 8))

        self._make_button(
            btn_box, "📂 Load Selected", BTN_GREEN, self.load_selected_solution,
            font=FONT_BUTTON_SMALL,
        ).pack(fill="x", pady=(0, 3))

        self._make_button(
            btn_box, "📋 Copy Solution", BTN_GRAY, self.copy_selected_solution,
            font=FONT_BUTTON_SMALL,
        ).pack(fill="x", pady=(0, 3))

        self._make_button(
            btn_box, "➕ Add Manual (B/D)", BTN_GRAY, self.open_manual_add_dialog,
            font=FONT_BUTTON_SMALL,
        ).pack(fill="x", pady=(0, 3))

        self._make_button(
            btn_box, "✏️ Rename Selected", BTN_GRAY, self.rename_selected_solution,
            font=FONT_BUTTON_SMALL,
        ).pack(fill="x", pady=(0, 3))

        btn_row = tk.Frame(btn_box, bg=CARD_BG)
        btn_row.pack(fill="x")

        self._make_button(
            btn_row, "❌ Delete", BTN_GRAY, self.delete_selected_solution,
            font=FONT_BUTTON_SMALL,
        ).pack(side="left", fill="x", expand=True, padx=(0, 2))

        self._make_button(
            btn_row, "🗑️ Clear All", BTN_RED, self.clear_all_saved_solutions,
            font=FONT_BUTTON_SMALL,
        ).pack(side="right", fill="x", expand=True, padx=(2, 0))

    def _build_default_sidebar(self, parent: tk.Widget) -> None:
        """Constructs the second sidebar for remote XML-fed default locations with a map selector."""
        self._make_section_label(parent, "MAP DEFAULT LOCATIONS", fg=ACCENT_CYAN).pack(
            fill="x", padx=10, pady=(8, 4)
        )

        self._make_divider(parent).pack(fill="x", padx=10, pady=(0, 6))

        map_frame = tk.Frame(parent, bg=CARD_BG)
        map_frame.pack(fill="x", padx=10, pady=(0, 6))

        self._make_field_label(map_frame, "Select Map").pack(fill="x", pady=(0, 1))

        self.map_dropdown = tk.OptionMenu(
            map_frame,
            self.selected_map_var,
            *(self.available_maps if self.available_maps else ["No Maps Found"]),
            command=lambda selected_map: [
                self.selected_map_var.set(selected_map),
                self.refresh_default_locations_list(),
            ],
        )
        self.map_dropdown.config(
            font=("Segoe UI", 9),
            fg=TEXT_LIGHT,
            bg=FIELD_BG,
            activebackground=BTN_GRAY,
            activeforeground=TEXT_LIGHT,
            bd=1,
            relief="solid",
            highlightthickness=0,
        )
        self.map_dropdown["menu"].config(
            bg=FIELD_BG,
            fg=TEXT_LIGHT,
            activebackground=BTN_GRAY,
            activeforeground=TEXT_LIGHT,
        )
        self.map_dropdown.pack(fill="x", ipady=1)

        list_frame = tk.Frame(parent, bg=CARD_BG)
        list_frame.pack(fill="both", expand=True, padx=8, pady=(0, 6))

        scrollbar = self._make_scrollbar(list_frame)
        self.listbox_defaults = self._make_listbox(list_frame, yscrollcommand=scrollbar.set)
        self.listbox_defaults.pack(side="left", fill="both", expand=True)
        scrollbar.config(command=self.listbox_defaults.yview)

        self.listbox_defaults.bind(
            "<Button-1>", lambda e: self._on_listbox_click(e, self.listbox_defaults)
        )
        self.listbox_defaults.bind(
            "<Double-Button-1>", lambda e: self.load_selected_default_location()
        )

        btn_box = tk.Frame(parent, bg=CARD_BG)
        btn_box.pack(fill="x", padx=8, pady=(0, 8))

        self._make_button(
            btn_box, "🎯 Load Default Target", BTN_GREEN, self.load_selected_default_location,
        ).pack(fill="x", pady=(0, 3), ipady=2)

        self._make_button(
            btn_box, "🔄 Reload XML Data", BTN_GRAY, self.reload_xml_data,
            font=FONT_BUTTON_SMALL,
        ).pack(fill="x", ipady=2)

        self.refresh_default_locations_list()

    def refresh_default_locations_list(self) -> None:
        """Refreshes the default locations listbox based on the chosen map filter."""
        if not self.has_xml:
            return
        self.listbox_defaults.delete(0, tk.END)
        current_map = self.selected_map_var.get()

        for loc in self.xml_locations:
            if loc["map"] == current_map:
                display_str = f"{loc['name']} ({loc['x']}, {loc['y']})"
                self.listbox_defaults.insert(tk.END, display_str)

    def reload_xml_data(self) -> None:
        """Reloads data from the remote XML URL and updates map choices and displayed entries."""
        self.load_xml_locations()
        if not self.has_xml:
            return

        menu = self.map_dropdown["menu"]
        menu.delete(0, "end")

        maps = self.available_maps if self.available_maps else ["No Maps Found"]
        for m in maps:
            menu.add_command(
                label=m,
                command=lambda val=m: [
                    self.selected_map_var.set(val),
                    self.refresh_default_locations_list(),
                ],
            )

        if maps and self.selected_map_var.get() not in maps:
            self.selected_map_var.set(maps[0])

        self.refresh_default_locations_list()

    def load_selected_default_location(self) -> None:
        """Loads coordinates from the selected default location into the target fields."""
        if not self.has_xml:
            return

        selection = self.listbox_defaults.curselection()
        if not selection:
            return

        selected_idx = selection[0]
        current_map = self.selected_map_var.get()

        matching_locs = [
            loc for loc in self.xml_locations if loc["map"] == current_map
        ]

        if selected_idx < len(matching_locs):
            chosen_loc = matching_locs[selected_idx]

            self.offset_x = 0.0
            self.offset_y = 0.0
            self.last_applied_impact = None
            self.target_x.set(chosen_loc["x"])
            self.target_y.set(chosen_loc["y"])
            self.update_live_solution()

    # --- FIELD FACTORIES ---

    def _create_field(
        self,
        parent: tk.Widget,
        label_text: str,
        text_var: tk.StringVar,
        row: int,
        col: int,
        placeholder: str = "",
    ) -> tk.Entry:
        """Factory method to build a styled labeled entry field."""
        f = tk.Frame(parent, bg=CARD_BG)
        f.grid(row=row, column=col, sticky="ew", padx=4, pady=2)

        self._make_field_label(f, label_text).pack(fill="x", pady=(0, 1))

        entry = self._make_entry(f, text_var)
        entry.pack(fill="x", ipady=2)

        if placeholder and not text_var.get():
            entry.insert(0, placeholder)
        return entry

    def _create_quick_paste_field(
        self,
        parent: tk.Widget,
        label_text: str,
        text_var: tk.StringVar,
        row: int,
        col: int,
        placeholder: str = "",
        columnspan: int = 1,
    ) -> tk.Entry:
        """Factory method to build an entry field with an integrated inline Paste button."""
        f = tk.Frame(parent, bg=CARD_BG)
        f.grid(row=row, column=col, columnspan=columnspan, sticky="ew", padx=4, pady=2)

        self._make_field_label(f, label_text).pack(fill="x", pady=(0, 1))

        entry_frame = tk.Frame(f, bg=CARD_BG)
        entry_frame.pack(fill="x")

        entry = self._make_entry(entry_frame, text_var)
        entry.pack(side="left", fill="x", expand=True, ipady=2)

        self._make_button(
            entry_frame, "📋 Paste", BTN_GRAY,
            lambda: self._paste_clipboard_to_var(text_var),
            font=FONT_BUTTON_SMALL,
        ).pack(side="right", padx=(3, 0), ipady=1)

        if placeholder and not text_var.get():
            entry.insert(0, placeholder)
        return entry

    def _add_stat_row(
        self, parent: tk.Widget, label_text: str, row: int
    ) -> tk.Label:
        """Helper to create a standard key-value row inside the dispersion box."""
        tk.Label(
            parent,
            text=label_text,
            font=FONT_SECTION,
            fg=TEXT_MUTED,
            bg="#0f1118",
            anchor="w",
        ).grid(row=row, column=0, sticky="w", pady=2)

        value_lbl = tk.Label(
            parent,
            text="---",
            font=FONT_VALUE_LARGE,
            fg=TEXT_LIGHT,
            bg="#0f1118",
            anchor="e",
        )
        value_lbl.grid(row=row, column=1, sticky="e", pady=2)
        return value_lbl

    # --- TRACES & HANDLERS ---

    def _register_traces(self) -> None:
        """Registers reactive listener callbacks on variable mutations."""
        for var in (
            self.gun_x,
            self.gun_y,
            self.target_x,
            self.target_y,
            self.impact_x,
            self.impact_y,
            self.aoe_dist,
        ):
            var.trace_add("write", self.update_live_solution)

        self.gun_paste.trace_add(
            "write",
            lambda *args: self._apply_paste(self.gun_paste, self.gun_x, self.gun_y),
        )
        self.target_paste.trace_add(
            "write",
            lambda *args: self._apply_paste(
                self.target_paste, self.target_x, self.target_y, reset_offset=True
            ),
        )
        self.impact_paste.trace_add(
            "write",
            lambda *args: self._apply_paste(
                self.impact_paste, self.impact_x, self.impact_y
            ),
        )

    def _paste_clipboard_to_var(self, text_var: tk.StringVar) -> None:
        """Pastes current OS clipboard contents directly into a target StringVar."""
        try:
            clip_text = self.root.clipboard_get()
            text_var.set(clip_text)
        except tk.TclError:
            messagebox.showwarning("Clipboard Empty", "No text found in clipboard.")

    def _apply_paste(
        self,
        paste_var: tk.StringVar,
        x_var: tk.StringVar,
        y_var: tk.StringVar,
        reset_offset: bool = False,
    ) -> None:
        """Parses quick-set text input and updates destination X & Y variables."""
        raw_text = paste_var.get()
        x_val, y_val = parse_coords_string(raw_text)

        if x_val is not None and y_val is not None:
            if reset_offset:
                self.offset_x = 0.0
                self.offset_y = 0.0
                self.last_applied_impact = None
            x_var.set(x_val)
            y_var.set(y_val)

    # --- SAVED SOLUTIONS MANAGEMENT ---

    def save_current_solution(self) -> None:
        """Saves active solution with custom name into the sidebar list."""
        if self.current_bearing is None or self.current_distance is None:
            messagebox.showwarning("No Solution", "Calculate a valid solution first.")
            return

        name = self.solution_name_var.get().strip()
        if not name:
            name = f"Solution {self.solution_counter}"

        target_x_str = self.target_x.get()
        target_y_str = self.target_y.get()

        solution_data = {
            "name": name,
            "bearing": self.current_bearing,
            "distance": self.current_distance,
            "target_x": target_x_str,
            "target_y": target_y_str,
        }

        self.saved_solutions.append(solution_data)
        display_text = f"{name}: {self.current_bearing:05.1f}° | {self.current_distance:4.0f}m"
        self.listbox_saved.insert(tk.END, display_text)

        self.solution_counter += 1
        self.solution_name_var.set(f"Solution {self.solution_counter}")

    def load_selected_solution(self) -> None:
        """Loads selected item's target coordinates into the main input fields."""
        selection = self.listbox_saved.curselection()
        if not selection:
            return

        selected_idx = selection[0]

        if selected_idx < len(self.saved_solutions):
            data = self.saved_solutions[selected_idx]

            self.offset_x = 0.0
            self.offset_y = 0.0
            self.last_applied_impact = None
            self.target_x.set(data["target_x"])
            self.target_y.set(data["target_y"])
            self.update_live_solution()

    def copy_selected_solution(self) -> None:
        """Copies the selected saved solution formatted to the OS clipboard."""
        try:
            selected_idx = self.listbox_saved.curselection()[0]
            data = self.saved_solutions[selected_idx]
            formatted_text = (
                f"{data['name']} - {data['bearing']:05.1f}° | {data['distance']:.0f}m"
            )

            self.root.clipboard_clear()
            self.root.clipboard_append(formatted_text)
            self.root.update()
        except IndexError:
            messagebox.showwarning("Selection Required", "Select a saved solution to copy.")

    def rename_selected_solution(self) -> None:
        """Prompts for a new name and updates an already saved solution."""
        try:
            selected_idx = self.listbox_saved.curselection()[0]
            data = self.saved_solutions[selected_idx]
            current_name = data["name"]

            new_name = simpledialog.askstring(
                "Rename Solution",
                "Enter new name for the solution:",
                initialvalue=current_name,
                parent=self.root,
            )

            if new_name is not None:
                new_name = new_name.strip()
                if new_name:
                    data["name"] = new_name
                    display_text = f"{new_name}: {data['bearing']:05.1f}° | {data['distance']:4.0f}m"
                    self.listbox_saved.delete(selected_idx)
                    self.listbox_saved.insert(selected_idx, display_text)
                    self.listbox_saved.selection_set(selected_idx)
        except IndexError:
            messagebox.showwarning(
                "Selection Required", "Select a saved solution to rename."
            )

    def open_manual_add_dialog(self) -> None:
        """Opens a modal popup dialog centered over the main window to manually enter bearing and distance."""
        try:
            float(self.gun_x.get())
            float(self.gun_y.get())
        except ValueError:
            messagebox.showwarning(
                "Gun Coordinates Missing",
                "Please set valid Gunner X and Y coordinates first before manual entry.",
            )
            return

        dialog = tk.Toplevel(self.root)
        dialog.title("Add Solution by Bearing & Distance")

        dialog.update_idletasks()
        width = 320
        height = 280
        x = self.root.winfo_x() + (self.root.winfo_width() // 2) - (width // 2)
        y = self.root.winfo_y() + (self.root.winfo_height() // 2) - (height // 2)
        dialog.geometry(f"{width}x{height}+{x}+{y}")

        dialog.configure(bg=CARD_BG)
        dialog.transient(self.root)
        dialog.grab_set()

        self._make_section_label(
            dialog, "Manual Bearing & Distance Entry", fg=ACCENT_CYAN
        ).pack(pady=(12, 8))

        form_frame = tk.Frame(dialog, bg=CARD_BG)
        form_frame.pack(fill="x", padx=16)

        self._make_field_label(form_frame, "Solution Name:").pack(fill="x")
        name_var = tk.StringVar(value=f"Manual {self.solution_counter}")
        e_name = self._make_entry(form_frame, name_var, with_highlight=False)
        e_name.pack(fill="x", pady=(0, 6), ipady=2)

        self._make_field_label(form_frame, "Bearing (°):").pack(fill="x")
        bearing_var = tk.StringVar(value="")
        e_bearing = self._make_entry(form_frame, bearing_var, with_highlight=False)
        e_bearing.pack(fill="x", pady=(0, 6), ipady=2)

        self._make_field_label(form_frame, "Distance (m):").pack(fill="x")
        distance_var = tk.StringVar(value="")
        e_distance = self._make_entry(form_frame, distance_var, with_highlight=False)
        e_distance.pack(fill="x", pady=(0, 10), ipady=2)

        def submit_manual() -> None:
            try:
                b_val = float(bearing_var.get())
                d_val = float(distance_var.get())
                name_val = name_var.get().strip()
                if not name_val:
                    name_val = f"Manual {self.solution_counter}"

                gx = float(self.gun_x.get()) * 100.0
                gy = float(self.gun_y.get()) * 100.0

                b_rad = math.radians(b_val)
                dx = d_val * math.sin(b_rad)
                dy = d_val * math.cos(b_rad)

                tx = (gx + dx) / 100.0
                ty = (gy + dy) / 100.0

                solution_data = {
                    "name": name_val,
                    "bearing": (b_val + 360) % 360,
                    "distance": d_val,
                    "target_x": f"{tx:.2f}",
                    "target_y": f"{ty:.2f}",
                }

                self.saved_solutions.append(solution_data)
                display_text = (
                    f"{name_val}: {solution_data['bearing']:05.1f}° | {d_val:4.0f}m"
                )
                self.listbox_saved.insert(tk.END, display_text)

                self.solution_counter += 1
                self.solution_name_var.set(f"Solution {self.solution_counter}")
                dialog.destroy()

            except ValueError:
                messagebox.showerror(
                    "Invalid Input",
                    "Please enter valid numerical values for bearing and distance.",
                    parent=dialog,
                )

        self._make_button(dialog, "Save to Table", BTN_GREEN, submit_manual).pack(
            fill="x", padx=16, pady=(4, 0), ipady=3
        )

    def delete_selected_solution(self) -> None:
        """Removes the selected solution entry from the listbox."""
        try:
            selected_idx = self.listbox_saved.curselection()[0]
            self.listbox_saved.delete(selected_idx)
            del self.saved_solutions[selected_idx]
        except IndexError:
            messagebox.showwarning("Selection Required", "Select a solution to delete.")

    def clear_all_saved_solutions(self) -> None:
        """Clears all saved solution records after user confirmation."""
        if not self.saved_solutions:
            return

        if messagebox.askyesno(
            "Confirm Clear All",
            "Are you sure you want to delete ALL saved solutions?",
            parent=self.root,
        ):
            self.listbox_saved.delete(0, tk.END)
            self.saved_solutions.clear()
            self.solution_counter = 1
            self.solution_name_var.set("Solution 1")

    # --- CLIPBOARD MONITORING & RESET LOGIC ---

    def toggle_clipboard_watch(self) -> None:
        """Toggles background clipboard polling for automatic target updating."""
        self.is_watching_clipboard = not self.is_watching_clipboard
        if self.is_watching_clipboard:
            self.btn_auto_clip.config(
                text="📡 Auto-Target: ON",
                bg=BTN_GREEN,
                activebackground=BTN_HOVER[BTN_GREEN],
            )
            try:
                self.last_clipboard_text = self.root.clipboard_get().strip()
            except tk.TclError:
                self.last_clipboard_text = ""
            self.poll_clipboard()
        else:
            self.btn_auto_clip.config(
                text="📡 Auto-Target: OFF",
                bg=BTN_GRAY,
                activebackground=BTN_HOVER[BTN_GRAY],
            )

    def poll_clipboard(self) -> None:
        """Periodically checks the OS clipboard for updated coordinate strings."""
        if not self.is_watching_clipboard:
            return

        try:
            current_clip = self.root.clipboard_get().strip()
            if current_clip and current_clip != self.last_clipboard_text:
                self.last_clipboard_text = current_clip
                x_val, y_val = parse_coords_string(current_clip)
                if x_val is not None and y_val is not None:
                    if self.shot_counter == 0:
                        self.target_paste.set(current_clip)
        except tk.TclError:
            pass

        if self.is_watching_clipboard:
            self.root.after(500, self.poll_clipboard)

    def clear_all_inputs(self) -> None:
        """Clears all coordinate entry boxes, quick pastes, and accumulated offsets."""
        self.gun_x.set("")
        self.gun_y.set("")
        self.target_x.set("")
        self.target_y.set("")
        self.impact_x.set("")
        self.impact_y.set("")

        self.gun_paste.set("")
        self.target_paste.set("")
        self.impact_paste.set("")

        self.offset_x = 0.0
        self.offset_y = 0.0
        self.last_applied_impact = None

        self.clear_miss_log()
        self.hide_miss_log()

        self.update_live_solution()

    # --- CALCULATION & CORRECTION LOGIC ---

    def update_live_solution(self, *args) -> None:
        """Recalculates bearing, distance, AOE dispersion boundaries, and range indicators."""
        if not hasattr(self, "lbl_bearing"):
            return

        try:
            gx = float(self.gun_x.get())
            gy = float(self.gun_y.get())
            tx = float(self.target_x.get()) + self.offset_x
            ty = float(self.target_y.get()) + self.offset_y
            aoe = float(self.aoe_dist.get())

            res = BallisticsEngine.calculate_solution(gx, gy, tx, ty, aoe)

            self.current_bearing = res["bearing"]
            self.current_distance = res["distance"]

            self.lbl_bearing.config(text=f"Bearing: {res['bearing']:.1f}°")
            self.lbl_distance.config(text=f"Distance: {res['distance']:.1f} m")

            self.lbl_disp_bearing.config(
                text=f"{res['min_bearing']:.1f}° – {res['max_bearing']:.1f}° (±{res['delta_bearing']:.1f}°)"
            )
            self.lbl_disp_distance.config(
                text=f"{res['min_distance']:.0f} m – {res['max_distance']:.0f} m (±{res['radius']:.0f} m)"
            )
            self.lbl_disp_area.config(text=f"{res['area']:,.0f} m²")

            distance = res["distance"]

            if 780.0 <= distance <= 2629.0:
                self.lbl_sph2_indicator.config(fg=RANGE_IN)
            else:
                self.lbl_sph2_indicator.config(fg=RANGE_OUT)

            if 119.0 <= distance <= 684.0:
                self.lbl_mortar_indicator.config(fg=RANGE_IN)
            else:
                self.lbl_mortar_indicator.config(fg=RANGE_OUT)

        except ValueError:
            self.current_bearing = None
            self.current_distance = None

            self.lbl_bearing.config(text="Bearing: ---°")
            self.lbl_distance.config(text="Distance: --- m")
            self.lbl_disp_bearing.config(text="0° – 0° (±0°)")
            self.lbl_disp_distance.config(text="0 m – 0 m (±0 m)")
            self.lbl_disp_area.config(text="0 m²")

            self.lbl_sph2_indicator.config(fg=TEXT_MUTED)
            self.lbl_mortar_indicator.config(fg=TEXT_MUTED)

        # Update visual plotter
        self.update_impact_visualizer()

    def update_impact_visualizer(self) -> None:
        """Renders dynamic 1:1 true-scale 2D plot with a distance grid background."""
        if not hasattr(self, "canvas_vis"):
            return

        self.canvas_vis.delete("all")
        c_w = self.canvas_vis.winfo_width()
        c_h = self.canvas_vis.winfo_height()

        if c_w <= 10 or c_h <= 10:
            c_w, c_h = 220, 230

        points = []
        try:
            gx, gy = float(self.gun_x.get()), float(self.gun_y.get())
            points.append(("gun", gx, gy))
        except ValueError:
            gx, gy = None, None

        try:
            raw_tx, raw_ty = float(self.target_x.get()), float(self.target_y.get())
            tx, ty = raw_tx + self.offset_x, raw_ty + self.offset_y
            points.append(("target", raw_tx, raw_ty))
            points.append(("aim", tx, ty))
        except ValueError:
            raw_tx, raw_ty = None, None
            tx, ty = None, None

        for shot in self.miss_history:
            points.append(("history_impact", shot["x"], shot["y"]))

        try:
            ix, iy = float(self.impact_x.get()), float(self.impact_y.get())
            points.append(("current_impact", ix, iy))
        except ValueError:
            ix, iy = None, None

        if gx is None or tx is None:
            self.canvas_vis.create_text(
                c_w // 2,
                c_h // 2,
                text="Set Gun & Target\ncoordinates to view plot",
                fill=TEXT_MUTED,
                font=FONT_LABEL,
                justify="center",
            )
            return

        all_x = [p[1] for p in points]
        all_y = [p[2] for p in points]

        min_x, max_x = min(all_x), max(all_x)
        min_y, max_y = min(all_y), max(all_y)

        span_x = max_x - min_x
        span_y = max_y - min_y

        min_span = 0.5
        if span_x < min_span:
            mid_x = (min_x + max_x) / 2.0
            min_x = mid_x - min_span / 2.0
            max_x = mid_x + min_span / 2.0
            span_x = min_span

        if span_y < min_span:
            mid_y = (min_y + max_y) / 2.0
            min_y = mid_y - min_span / 2.0
            max_y = mid_y + min_span / 2.0
            span_y = min_span

        margin = 35
        usable_w = c_w - 2 * margin
        usable_h = c_h - 2 * margin

        scale = min(usable_w / span_x, usable_h / span_y)

        center_world_x = (min_x + max_x) / 2.0
        center_world_y = (min_y + max_y) / 2.0
        center_canvas_x = c_w / 2.0
        center_canvas_y = c_h / 2.0

        def to_canvas(x, y):
            cx = center_canvas_x + (x - center_world_x) * scale
            cy = center_canvas_y - (y - center_world_y) * scale
            return cx, cy

        span_meters = max(span_x, span_y) * 100.0
        grid_steps_m = [10, 25, 50, 100, 250, 500, 1000]
        step_m = grid_steps_m[0]
        for s in grid_steps_m:
            if span_meters / s <= 7:
                step_m = s
                break

        step_coord = step_m / 100.0

        world_min_x = center_world_x - (c_w / (2.0 * scale))
        world_max_x = center_world_x + (c_w / (2.0 * scale))
        world_min_y = center_world_y - (c_h / (2.0 * scale))
        world_max_y = center_world_y + (c_h / (2.0 * scale))

        start_grid_x = math.floor(world_min_x / step_coord) * step_coord
        end_grid_x = math.ceil(world_max_x / step_coord) * step_coord

        start_grid_y = math.floor(world_min_y / step_coord) * step_coord
        end_grid_y = math.ceil(world_max_y / step_coord) * step_coord

        curr_x = start_grid_x
        while curr_x <= end_grid_x:
            cx, _ = to_canvas(curr_x, 0)
            if 0 <= cx <= c_w:
                self.canvas_vis.create_line(cx, 0, cx, c_h, fill="#232633", width=1, dash=(2, 4))
                self.canvas_vis.create_text(
                    cx + 2, c_h - 8, text=f"{curr_x:.1f}", fill="#51576d", font=("Segoe UI", 7), anchor="w"
                )
            curr_x += step_coord

        curr_y = start_grid_y
        while curr_y <= end_grid_y:
            _, cy = to_canvas(0, curr_y)
            if 0 <= cy <= c_h:
                self.canvas_vis.create_line(0, cy, c_w, cy, fill="#232633", width=1, dash=(2, 4))
                self.canvas_vis.create_text(
                    4, cy - 6, text=f"{curr_y:.1f}", fill="#51576d", font=("Segoe UI", 7), anchor="w"
                )
            curr_y += step_coord

        self.canvas_vis.create_text(
            c_w - 6, 8, text=f"Grid Step: {step_m}m (1:1 Scale)", fill=ACCENT_CYAN, font=("Segoe UI", 7, "bold"), anchor="e"
        )

        cgx, cgy = to_canvas(gx, gy)
        ctx, cty = to_canvas(tx, ty)
        crtx, crty = to_canvas(raw_tx, raw_ty)

        self.canvas_vis.create_line(cgx, cgy, ctx, cty, fill="#8289a0", width=1.5, dash=(4, 4))

        for shot in self.miss_history:
            sh_x, sh_y = shot["x"], shot["y"]
            csh_x, csh_y = to_canvas(sh_x, sh_y)
            self.canvas_vis.create_line(cgx, cgy, csh_x, csh_y, fill="#404452", width=1, dash=(2, 2))
            r = 5
            self.canvas_vis.create_oval(
                csh_x - r, csh_y - r, csh_x + r, csh_y + r, fill="#c52828", outline="#ff8a80", width=1
            )
            self.canvas_vis.create_text(
                csh_x, csh_y - 10, text=f"#{shot['shot']}", fill="#ff8a80", font=("Segoe UI", 7, "bold")
            )

        if ix is not None and iy is not None:
            cix, ciy = to_canvas(ix, iy)
            self.canvas_vis.create_line(cgx, cgy, cix, ciy, fill=TEXT_LIGHT, width=1.5)
            r = 6
            self.canvas_vis.create_oval(
                cix - r, ciy - r, cix + r, ciy + r, fill=RANGE_OUT, outline="#ffffff", width=1.5
            )
            self.canvas_vis.create_text(
                cix, ciy - 12, text="Impact", fill=RANGE_OUT, font=("Segoe UI", 8, "bold")
            )

        tr2 = 5
        self.canvas_vis.create_polygon(
            crtx, crty - tr2, crtx + tr2, crty, crtx, crty + tr2, crtx - tr2, crty,
            fill="#e14eca", outline="#f7b3ec", width=1.5,
        )
        self.canvas_vis.create_text(
            crtx, crty - 12, text="Target", fill="#e14eca", font=("Segoe UI", 8, "bold")
        )

        if self.offset_x != 0.0 or self.offset_y != 0.0:
            tr = 6
            self.canvas_vis.create_line(ctx - tr - 2, cty, ctx + tr + 2, cty, fill=ACCENT_CYAN, width=2)
            self.canvas_vis.create_line(ctx, cty - tr - 2, ctx, cty + tr + 2, fill=ACCENT_CYAN, width=2)
            self.canvas_vis.create_text(
                ctx, cty + 14, text="Aim Point", fill=ACCENT_CYAN, font=("Segoe UI", 8, "bold")
            )

        gr = 6
        self.canvas_vis.create_oval(
            cgx - gr, cgy - gr, cgx + gr, cgy + gr, fill=BTN_GREEN, outline=RANGE_IN, width=1.5
        )
        self.canvas_vis.create_text(
            cgx, cgy + 14, text="Gunner", fill=RANGE_IN, font=("Segoe UI", 8, "bold")
        )

    def apply_miss_correction(self) -> None:
        """Applies offset based on spotter impact coordinates, logs shot error distance, opens side log, and recalculates solution."""
        try:
            imp_x = float(self.impact_x.get())
            imp_y = float(self.impact_y.get())

            tgt_x = float(self.target_x.get())
            tgt_y = float(self.target_y.get())

            if self.last_applied_impact == (imp_x, imp_y):
                messagebox.showwarning(
                    "Same Impact Coordinates",
                    "These Impact X/Y values were already applied to the last "
                    "correction. Enter the new shot's impact coordinates before "
                    "clicking Confirm Miss again.",
                )
                return

            dx = (imp_x - tgt_x) * 100.0
            dy = (imp_y - tgt_y) * 100.0
            error_dist = math.hypot(dx, dy)

            self.shot_counter += 1
            self.miss_history.append(
                {
                    "shot": self.shot_counter,
                    "error_dist": error_dist,
                    "x": imp_x,
                    "y": imp_y,
                }
            )

            display_row = f" #{self.shot_counter:<6} | {error_dist:8.1f} m"
            self.listbox_misses.insert(tk.END, display_row)
            self.listbox_misses.see(tk.END)

            self.show_miss_log()

            self.offset_x -= imp_x - tgt_x
            self.offset_y -= imp_y - tgt_y
            self.last_applied_impact = (imp_x, imp_y)

            self.update_live_solution()

        except ValueError:
            messagebox.showerror(
                "Error", "Please enter valid numerical impact coordinates."
            )

    def confirm_hit(self) -> None:
        """Updates main target directly to impact coordinates and clears accumulated offsets."""
        try:
            self.offset_x = 0.0
            self.offset_y = 0.0
            self.last_applied_impact = None
            self.target_x.set(self.impact_x.get())
            self.target_y.set(self.impact_y.get())
            self.update_live_solution()

        except ValueError:
            messagebox.showerror(
                "Error", "Please enter valid numerical impact coordinates."
            )

    def reset_corrections(self) -> None:
        """Resets all accumulated spotter corrections, wipes impact inputs, clears the miss log, and closes the sidebar."""
        self.offset_x = 0.0
        self.offset_y = 0.0
        self.last_applied_impact = None

        self.impact_x.set("")
        self.impact_y.set("")
        self.impact_paste.set("")

        self.clear_miss_log()
        self.hide_miss_log()

        self.update_live_solution()


if __name__ == "__main__":
    root = tk.Tk()
    app = VortexArtyCalculator(root)
    root.mainloop()