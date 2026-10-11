"""
ORB RUSH  -  a neon maze game, Easy to Extreme
Pure Python (tkinter only, no installs needed).

MODES
  1  ONE PLAYER     : roll your orb to the target (A* hint / A* auto-solve available)
  2  TWO PLAYERS    : race!  Player 1 = ARROW keys, Player 2 = W A S D
  3  VS COMPUTER    : race an orb driven by the A* algorithm

KEYS
  Arrows / WASD : move (solo and vs-computer: both work)
  H             : show / hide the A* hint path   (solo + vs-computer)
  E             : show / hide the cells A* explored
  SPACE         : A* auto-solve (solo only)
  R             : new maze      M : menu      ESC (in menu) : back
  ENTER         : next level after a win
"""
import heapq
import math
import random
import time
import tkinter as tk
import tkinter.font as tkfont

# ---------- Design ----------
BG_TOP = "#1a1736"          # window gradient (top -> bottom)
BG_BOT = "#0a0914"
BG = BG_BOT
PANEL = "#1b1930"
FLOOR = "#0b0a16"           # maze floor
DARK = "#12101f"
LINE = "#3a3763"
TEXT = "#f4f2ff"
MUTED = "#9d9ac4"

YEL = "#ffd23f"
TEAL = "#22e0cf"
ORG = "#ff8a2a"
PINK = "#ff5fa2"
BLUE = "#4a8cff"
GREEN = "#D4AF37"
PURPLE = "#b98cff"
PAL = [YEL, TEAL, ORG, PINK, BLUE]
WALL_GRADIENT = [TEAL, BLUE, "#a56bff", PINK, ORG, YEL]   # walls shift colour corner to corner

# Layout (chosen at start-up so the window fits small laptop screens too)
W, H = 720, 840
MAZE_TOP = 120
MAZE_MAX = 640

DIRS = {"N": (0, -1), "S": (0, 1), "E": (1, 0), "W": (-1, 0)}
OPP = {"N": "S", "S": "N", "E": "W", "W": "E"}
ARROWS = {"up": "N", "down": "S", "left": "W", "right": "E"}
WASD = {"w": "N", "s": "S", "a": "W", "d": "E"}
BOTH = {**ARROWS, **WASD}
ALL_MOVE_KEYS = set(BOTH)

# name, cells per side, extra loops (more routes => A* matters), colour
LEVELS = [
    ("EASY", 10, 0.00, TEAL),
    ("MEDIUM", 16, 0.03, YEL),
    ("HARD", 24, 0.06, ORG),
    ("EXTREME", 34, 0.09, PINK),
]
LEVEL_DESC = ["10 x 10 grid, one winding route",
              "16 x 16 grid, a few shortcuts",
              "24 x 24 grid, loops everywhere",
              "34 x 34 grid, a true labyrinth"]
MODES = [("ONE PLAYER", TEAL, "Roll to the target, A* can help", [ORG]),
         ("TWO PLAYERS", PINK, "Race a friend: arrows vs W A S D", [ORG, GREEN]),
         ("VS COMPUTER", ORG, "Race an orb driven by A*", [ORG, PURPLE])]

FONTS = {"display": "Arial Black", "ui": "Segoe UI", "mono": "Consolas"}


def setup_fonts(root):
    """Pick the nicest installed font for each role (falls back gracefully)."""
    try:
        have = set(tkfont.families(root))
    except Exception:
        return

    def pick(options):
        for o in options:
            if o in have:
                return o
        return options[-1]

    FONTS["display"] = pick(["Arial Black", "Impact", "Avenir Next", "Helvetica Neue",
                             "DejaVu Sans", "Arial"])
    FONTS["ui"] = pick(["Segoe UI", "SF Pro Text", "Helvetica Neue", "Ubuntu",
                        "DejaVu Sans", "Arial"])
    FONTS["mono"] = pick(["Consolas", "Menlo", "DejaVu Sans Mono", "Courier New", "Courier"])


def F(kind, size, bold=True):
    return (FONTS[kind], size, "bold" if bold else "normal")


def apply_layout(screen_h):
    """Big window on tall screens, compact window on small ones (e.g. 768px laptops)."""
    global H, MAZE_MAX
    if screen_h >= 900:
        H, MAZE_MAX = 840, 640
    else:
        H, MAZE_MAX = 760, 560


# ---------- colour + drawing helpers ----------
def _rgb(c):
    c = c.lstrip("#")
    return int(c[0:2], 16), int(c[2:4], 16), int(c[4:6], 16)


def mix(a, b, t):
    """Blend colour a -> b (t = 0 gives a, t = 1 gives b)."""
    t = max(0.0, min(1.0, t))
    ra, ga, ba = _rgb(a)
    rb, gb, bb = _rgb(b)
    return "#%02x%02x%02x" % (int(ra + (rb - ra) * t), int(ga + (gb - ga) * t), int(ba + (bb - ba) * t))


def tint(color, base, strength):
    """`color` at the given strength laid over `base` (a fake glow: tk has no alpha)."""
    return mix(base, color, strength)


def gradient_at(t):
    t = max(0.0, min(1.0, t)) * (len(WALL_GRADIENT) - 1)
    i = min(int(t), len(WALL_GRADIENT) - 2)
    return mix(WALL_GRADIENT[i], WALL_GRADIENT[i + 1], t - i)


def rrect(cv, x1, y1, x2, y2, r=12, **kw):
    """Rounded rectangle (smooth polygon)."""
    r = min(r, (x2 - x1) / 2, (y2 - y1) / 2)
    pts = [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r, x2, y2 - r, x2, y2,
           x2 - r, y2, x1 + r, y2, x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]
    return cv.create_polygon(pts, smooth=True, **kw)


def glow_rrect(cv, x1, y1, x2, y2, r, color, base, layers=((10, .10), (6, .22), (3, .45)), **kw):
    """Soft neon halo around a rounded rectangle."""
    for w, t in layers:
        rrect(cv, x1, y1, x2, y2, r, fill="", outline=tint(color, base, t), width=w, **kw)


# ---------- Maze ----------
class Maze:
    def __init__(self, cols, rows, braid=0.0):
        self.cols, self.rows = cols, rows
        self.walls = [[set("NSEW") for _ in range(cols)] for _ in range(rows)]
        self._carve()
        self._braid(braid)
        self.goal = (cols - 1, rows - 1)

    def _remove(self, x, y, d):
        dx, dy = DIRS[d]
        self.walls[y][x].discard(d)
        self.walls[y + dy][x + dx].discard(OPP[d])

    def _carve(self):
        seen = {(0, 0)}
        stack = [(0, 0)]
        while stack:
            x, y = stack[-1]
            options = [(d, x + dx, y + dy) for d, (dx, dy) in DIRS.items()
                       if 0 <= x + dx < self.cols and 0 <= y + dy < self.rows
                       and (x + dx, y + dy) not in seen]
            if not options:
                stack.pop()
                continue
            d, nx, ny = random.choice(options)
            self._remove(x, y, d)
            seen.add((nx, ny))
            stack.append((nx, ny))

    def _braid(self, chance):
        if chance <= 0:
            return
        for y in range(self.rows):
            for x in range(self.cols):
                for d in "ES":
                    dx, dy = DIRS[d]
                    if (0 <= x + dx < self.cols and 0 <= y + dy < self.rows
                            and d in self.walls[y][x] and random.random() < chance):
                        self._remove(x, y, d)

    def neighbors(self, cell):
        x, y = cell
        for d, (dx, dy) in DIRS.items():
            if d not in self.walls[y][x]:
                yield (x + dx, y + dy)


# ---------- A* ----------
def astar(maze, start, goal):
    """Returns (path, explored_set). path = [start, ..., goal] ([] if unreachable)."""
    def h(c):  # Manhattan distance: admissible on a 4-direction grid
        return abs(c[0] - goal[0]) + abs(c[1] - goal[1])

    open_heap = [(h(start), 0, start)]
    g = {start: 0}
    came = {}
    closed = set()
    while open_heap:
        _, cost, cur = heapq.heappop(open_heap)
        if cur in closed:
            continue
        closed.add(cur)
        if cur == goal:
            path = [cur]
            while cur in came:
                cur = came[cur]
                path.append(cur)
            path.reverse()
            return path, closed
        for nb in maze.neighbors(cur):
            ng = cost + 1
            if ng < g.get(nb, 1e9):
                g[nb] = ng
                came[nb] = cur
                heapq.heappush(open_heap, (ng + h(nb), ng, nb))
    return [], closed


# ---------- Ball player ----------
class Player:
    def __init__(self, name, color, color2, keys, ai=False, speed=9.0):
        self.name, self.color, self.color2 = name, color, color2
        self.keys, self.ai, self.speed = keys, ai, speed
        self.reset((0, 0))

    def reset(self, start):
        self.cell = start
        self.bx, self.by = float(start[0]), float(start[1])
        self.target = None
        self.moves = 0
        self.held = []
        self.buffer = None
        self.queue = []             # A* path for the CPU / auto-solve
        self.auto = False
        self.roll = 0.0             # rolling angle (for the stripes on the ball)
        self.trail = []             # recent positions -> comet tail


# ---------- Game ----------
class Game:
    def __init__(self, root):
        self.root = root
        self.alive = True
        try:
            apply_layout(root.winfo_screenheight())
        except Exception:
            pass
        setup_fonts(root)
        self._fc = {}
        root.title("ORB RUSH - Easy to Extreme")
        root.resizable(False, False)
        root.protocol("WM_DELETE_WINDOW", self.quit)
        self.cv = tk.Canvas(root, width=W, height=H, bg=BG, highlightthickness=0)
        self.cv.pack()
        root.bind("<KeyPress>", self.key_down)
        root.bind("<KeyRelease>", self.key_up)
        root.bind("<FocusOut>", self.focus_lost)
        self.cv.bind("<Button-1>", self.click)
        self.cv.bind("<Motion>", self.motion)
        self.cv.bind("<Leave>", self.leave)

        self.pending = {}           # delayed key-releases (fixes Linux auto-repeat flicker)
        self.buttons = []
        self.menu_items = []
        self.hover = None
        self.players = []
        self.confetti = []
        self.state = "menu"
        self.menu_page = "mode"
        self.mode = 0
        self.level = 0
        self.last = time.time()

        self.menu_maze = Maze(12, 14, 0.05)
        self.menu_colors = {(x, y, d): random.choice(PAL)
                            for y in range(14) for x in range(12) for d in "NW"}
        self.orbs = [{"x": random.uniform(0, W), "y": random.uniform(0, H + 80),
                      "r": random.uniform(2.5, 6.5), "vy": random.uniform(8, 26),
                      "ax": random.uniform(8, 28), "sp": random.uniform(.4, 1.2),
                      "ph": random.uniform(0, 6.28), "c": random.choice(PAL)} for _ in range(16)]
        self.show_menu("mode")
        self.tick()

    def quit(self):
        self.alive = False
        self.root.destroy()

    # ----- small helpers -----
    def tkf(self, kind, size, bold=True):
        key = (kind, size, bold)
        if key not in self._fc:
            self._fc[key] = tkfont.Font(root=self.root, family=FONTS[kind], size=size,
                                        weight="bold" if bold else "normal")
        return self._fc[key]

    def draw_bg(self):
        cv, bands = self.cv, 56
        for i in range(bands):
            y0, y1 = i * H / bands, (i + 1) * H / bands + 1
            cv.create_rectangle(0, y0, W, y1, fill=mix(BG_TOP, BG_BOT, i / (bands - 1)),
                                outline="", tags="bg")

    def draw_frame(self):
        cv = self.cv
        glow_rrect(cv, 8, 8, W - 8, H - 8, 24, YEL, BG_BOT, layers=((8, .05), (4, .12)))
        rrect(cv, 8, 8, W - 8, H - 8, 24, fill="", outline=tint(YEL, BG_BOT, .5), width=2)

    def draw_keys(self, items, cx, cy, tag, maxw=620):
        """A row of little keycaps with a label after each one, centred on cx."""
        for size in (10, 9, 8):
            fk, fl = self.tkf("ui", size, True), self.tkf("ui", size, False)
            dims = [(fk.measure(k) + 18, fl.measure(l)) for k, l in items]
            total = sum(kw + 6 + lw for kw, lw in dims) + 16 * (len(items) - 1)
            if total <= maxw:
                break
        cv, x = self.cv, cx - total / 2
        for (k, label), (kw, lw) in zip(items, dims):
            rrect(cv, x, cy - 9, x + kw, cy + 13, 6, fill="#161431", outline="", tags=tag)
            rrect(cv, x, cy - 13, x + kw, cy + 9, 6, fill="#2b2850", outline="#47437a", width=1, tags=tag)
            cv.create_text(x + kw / 2, cy - 2, text=k, fill=TEXT, font=F("ui", size), tags=tag)
            cv.create_text(x + kw + 6, cy - 2, text=label, anchor="w", fill=MUTED,
                           font=F("ui", size, False), tags=tag)
            x += kw + 6 + lw + 16

    # ----- menu -----
    def show_menu(self, page):
        self.state, self.menu_page = "menu", page
        self.hover = None
        cv = self.cv
        cv.config(cursor="")
        cv.delete("all")
        self.buttons = []
        self.draw_bg()

        # backdrop: the old maze art, now dimmed so the buttons can lead
        cs, m = 60, self.menu_maze
        for y in range(m.rows):
            for x in range(m.cols):
                for d in "NW":
                    if d not in m.walls[y][x]:
                        continue
                    col = tint(self.menu_colors[(x, y, d)], mix(BG_TOP, BG_BOT, y * cs / H), .14)
                    if d == "N" and y > 0:
                        cv.create_line(x * cs, y * cs, (x + 1) * cs, y * cs, width=9,
                                       fill=col, capstyle="round", tags="menuart")
                    if d == "W" and x > 0:
                        cv.create_line(x * cs, y * cs, x * cs, (y + 1) * cs, width=9,
                                       fill=col, capstyle="round", tags="menuart")

        # title: extruded gold letters
        for i, word in enumerate(("ORB", "RUSH")):
            y = 92 + i * 82
            for d in range(7, 0, -1):
                cv.create_text(W // 2 + d * .6, y + d, text=word, fill=mix("#8a6400", "#2a1d00", d / 7),
                               font=F("display", 62))
            cv.create_text(W // 2, y, text=word, fill=YEL, font=F("display", 62))

        # tagline: the four difficulty colours as a little track
        cv.create_line(W // 2 - 84, 238, W // 2 + 84, 238, fill=LINE, width=3, capstyle="round")
        for i, (_, _, _, col) in enumerate(LEVELS):
            x = W // 2 - 84 + i * 56
            cv.create_oval(x - 9, 229, x + 9, 247, fill=tint(col, BG_BOT, .25), outline="")
            cv.create_oval(x - 6, 232, x + 6, 244, fill=col, outline="")
        cv.create_text(W // 2, 264, text="from easy to extreme", fill=MUTED, font=F("ui", 11, False))

        # section heading
        label = "Choose a mode" if page == "mode" else "Choose a level"
        tw = self.tkf("ui", 13).measure(label)
        cv.create_text(W // 2, 306, text=label, fill=TEXT, font=F("ui", 13))
        cv.create_line(120, 306, W // 2 - tw / 2 - 16, 306, fill=LINE, width=2)
        cv.create_line(W // 2 + tw / 2 + 16, 306, W - 120, 306, fill=LINE, width=2)

        if page == "mode":
            self.menu_items = [dict(title=n, desc=d, col=c, marks=mk) for n, c, d, mk in MODES]
        else:
            self.menu_items = []
            for i, (name, n, _, col) in enumerate(LEVELS):
                marks = [col] * (i + 1) + [LINE] * (3 - i)
                self.menu_items.append(dict(title=name, desc=LEVEL_DESC[i], col=col, marks=marks))
        for i in range(len(self.menu_items)):
            y1 = 338 + i * 78
            self.buttons.append(((120, y1, W - 120, y1 + 62), i))
        self.draw_buttons()

        hints = ([("1-3", "pick a mode"), ("Click", "choose")] if page == "mode"
                 else [("1-4", "pick a level"), ("Click", "choose"), ("Esc", "back")])
        self.draw_keys(hints, W // 2, H - 36, "keys")
        self.draw_frame()

    def draw_buttons(self):
        cv = self.cv
        cv.delete("btn")
        for (rect, i) in self.buttons:
            it = self.menu_items[i]
            col, hov = it["col"], (i == self.hover)
            x1, y1, x2, y2 = rect
            if hov:
                x1, x2, y1, y2 = x1 - 5, x2 + 5, y1 - 2, y2 + 2
                glow_rrect(cv, x1, y1, x2, y2, 18, col, BG_BOT, layers=((12, .08), (7, .18), (3, .4)),
                           tags="btn")
            rrect(cv, x1, y1, x2, y2, 18, fill="#292650" if hov else PANEL,
                  outline=col if hov else tint(col, PANEL, .5), width=3 if hov else 2, tags="btn")
            cy = (y1 + y2) / 2
            # number badge
            cv.create_oval(x1 + 16, cy - 21, x1 + 58, cy + 21, fill=tint(col, PANEL, .25), outline="", tags="btn")
            cv.create_oval(x1 + 20, cy - 17, x1 + 54, cy + 17, fill=col, outline="", tags="btn")
            cv.create_text(x1 + 37, cy, text=str(i + 1), fill=DARK, font=F("display", 16), tags="btn")
            cv.create_text(x1 + 76, cy - 11, text=it["title"], anchor="w", fill=TEXT,
                           font=F("display", 16), tags="btn")
            cv.create_text(x1 + 76, cy + 13, text=it["desc"], anchor="w", fill=MUTED,
                           font=F("ui", 10, False), tags="btn")
            # right-hand marks: orbs for modes, difficulty pips for levels
            mx = x2 - 28
            for mc in reversed(it["marks"]):
                cv.create_oval(mx - 8, cy - 8, mx + 8, cy + 8, fill=mc, outline="", tags="btn")
                if mc != LINE:
                    cv.create_oval(mx - 5, cy - 6, mx - 1, cy - 2, fill=mix(mc, "#ffffff", .6),
                                   outline="", tags="btn")
                mx -= 24

    def draw_menu_orbs(self, now):
        cv = self.cv
        cv.delete("orb")
        for o in self.orbs:
            x = o["x"] + math.sin(now * o["sp"] + o["ph"]) * o["ax"]
            y = (o["y"] - now * o["vy"]) % (H + 80) - 40
            base = mix(BG_TOP, BG_BOT, min(1, max(0, y / H)))
            for s, t in ((2.8, .07), (1.8, .16), (1.0, .6)):
                r = o["r"] * s
                cv.create_oval(x - r, y - r, x + r, y + r, fill=tint(o["c"], base, t), outline="", tags="orb")
        cv.tag_lower("orb", "menuart")

    def menu_pick(self, i):
        self.hover = None
        if self.menu_page == "mode":
            if 0 <= i < len(MODES):
                self.mode = i
                self.show_menu("level")
        elif 0 <= i < len(LEVELS):
            self.start_level(i)

    def hit(self, e):
        for (x1, y1, x2, y2), i in self.buttons:
            if x1 <= e.x <= x2 and y1 <= e.y <= y2:
                return i
        return None

    def click(self, e):
        if self.state != "menu":
            return
        i = self.hit(e)
        if i is not None:
            self.menu_pick(i)

    def motion(self, e):
        if self.state != "menu":
            return
        h = self.hit(e)
        if h != self.hover:
            self.hover = h
            self.cv.config(cursor="hand2" if h is not None else "")
            self.draw_buttons()

    def leave(self, _e=None):
        if self.state == "menu" and self.hover is not None:
            self.hover = None
            self.cv.config(cursor="")
            self.draw_buttons()

    # ----- level setup -----
    def start_level(self, idx):
        self.level = idx
        _, n, braid, _ = LEVELS[idx]
        self.maze = Maze(n, n, braid)
        self.n = n
        self.cs = MAZE_MAX // n
        self.ox = (W - self.cs * n) // 2
        self.oy = MAZE_TOP
        self.cv.config(cursor="")

        if self.mode == 0:
            self.players = [Player("YOU", ORG, "#b8560a", BOTH)]
            starts = [(0, 0)]
        elif self.mode == 1:
            self.players = [Player("P1", ORG, "#b8560a", ARROWS), Player("P2", GREEN, "#3fa31f", WASD)]
            starts = [(0, 0), (n - 1, 0)]
            self.maze.goal = (n // 2, n - 1)
        else:
            self.players = [Player("YOU", ORG, "#b8560a", BOTH),
                            Player("CPU", PURPLE, "#6b3fc4", {}, ai=True, speed=4.5 + idx)]
            starts = [(0, 0), (n - 1, 0)]
            self.maze.goal = (n // 2, n - 1)
        for p, s in zip(self.players, starts):
            p.reset(s)

        self.t0 = None              # timer starts at the first move
        self.t_end = None
        self.winner = None
        self.confetti = []
        self.hint = False
        self.show_explored = False
        self.explored = set()
        self.path = []
        for k in list(self.pending):
            self.root.after_cancel(self.pending.pop(k))
        self.state = "play"
        self.compute_hint()
        self.draw_static()

    def compute_hint(self):
        self.path, self.explored = astar(self.maze, self.players[0].cell, self.maze.goal)

    def footer_keys(self):
        if self.mode == 0:
            return [("Arrows / WASD", "move"), ("H", "hint"), ("E", "explored"),
                    ("Space", "A* solve"), ("R", "new maze"), ("M", "menu")]
        if self.mode == 1:
            return [("Arrows", "player 1"), ("W A S D", "player 2"), ("R", "new maze"), ("M", "menu")]
        return [("Arrows / WASD", "move"), ("H", "hint"), ("E", "explored"),
                ("R", "new maze"), ("M", "menu")]

    def draw_static(self):
        cv = self.cv
        cv.delete("all")
        self.draw_bg()
        cs, ox, oy, n = self.cs, self.ox, self.oy, self.n
        size = cs * n
        wt = max(3, cs // 7)
        lvl_name, _, _, lvl_col = LEVELS[self.level]
        p0 = self.players[0]

        # --- header panel ---
        glow_rrect(cv, 30, 14, W - 30, 106, 20, lvl_col, BG_TOP, layers=((7, .05), (3, .12)))
        rrect(cv, 30, 14, W - 30, 106, 20, fill=PANEL, outline=LINE, width=2)
        lab = F("ui", 9, False)
        if self.mode == 0:
            cv.create_text(60, 34, text="Moves", anchor="w", fill=MUTED, font=lab)
            rrect(cv, W - 190, 24, W - 56, 62, 19, fill=tint(lvl_col, PANEL, .16), outline=lvl_col, width=2)
            cv.create_text(W - 123, 43, text=lvl_name, fill=lvl_col, font=F("display", 13))
        else:
            p1 = self.players[1]
            cv.create_text(60, 34, text=p0.name, anchor="w", fill=p0.color, font=F("ui", 10))
            cv.create_text(W - 60, 34, text=p1.name, anchor="e", fill=p1.color, font=F("ui", 10))
        cv.create_text(W // 2, 34, text="Time", fill=MUTED, font=lab)

        # --- maze floor ---
        glow_rrect(cv, ox - 9, oy - 9, ox + size + 9, oy + size + 9, 14, YEL, BG_TOP,
                   layers=((9, .06), (5, .14)))
        rrect(cv, ox - 9, oy - 9, ox + size + 9, oy + size + 9, 14, fill=FLOOR,
              outline=tint(YEL, FLOOR, .5), width=2)

        # start markers
        for p in self.players:
            sx, sy = self.cpx(*p.cell)
            r = cs * 0.40
            cv.create_oval(sx - r, sy - r, sx + r, sy + r, outline=tint(p.color, FLOOR, .55),
                           width=2, dash=(3, 3))

        # --- neon walls: layered lines fake a glow, colour drifts corner to corner ---
        m = self.maze
        segs = []
        span = max(1, 2 * (n - 1))
        for y in range(n):
            for x in range(n):
                w = m.walls[y][x]
                x0, y0 = ox + x * cs, oy + y * cs
                col = gradient_at((x + y) / span)
                if "N" in w and y > 0:
                    segs.append((x0, y0, x0 + cs, y0, col))
                if "W" in w and x > 0:
                    segs.append((x0, y0, x0, y0 + cs, col))
        layers = ([(wt + 9, .10), (wt + 5, .24), (wt, 1.0)] if wt >= 5
                  else [(wt + 5, .20), (wt, 1.0)])
        for lw, t in layers:
            for x0, y0, x1, y1, col in segs:
                cv.create_line(x0, y0, x1, y1, width=lw, fill=tint(col, FLOOR, t), capstyle="round")
        if wt >= 5:                                  # bright core, like a neon tube
            for x0, y0, x1, y1, col in segs:
                cv.create_line(x0, y0, x1, y1, width=max(1, wt // 3), fill=mix(col, "#ffffff", .55),
                               capstyle="round")
        glow_rrect(cv, ox, oy, ox + size, oy + size, 3, YEL, FLOOR, layers=((wt + 8, .10), (wt + 4, .24)))
        rrect(cv, ox, oy, ox + size, oy + size, 3, fill="", outline=YEL, width=wt)

        # --- footer ---
        rrect(cv, 30, H - 58, W - 30, H - 14, 16, fill=PANEL, outline=LINE, width=2)
        self.draw_keys(self.footer_keys(), W // 2, H - 36, "keys")
        self.draw_frame()

    def cpx(self, x, y):
        """Cell coordinates (may be fractional) -> canvas pixels of the cell centre."""
        return self.ox + (x + 0.5) * self.cs, self.oy + (y + 0.5) * self.cs

    # ----- input -----
    def key_down(self, e):
        k = e.keysym.lower()
        if k in self.pending:                       # key is auto-repeating: cancel its release
            self.root.after_cancel(self.pending.pop(k))

        if self.state == "menu":
            if k.isdigit():
                self.menu_pick(int(k) - 1)
            elif k == "escape" and self.menu_page == "level":
                self.show_menu("mode")
            return
        if k == "m":
            self.show_menu("mode")
            return
        if k == "r":
            self.start_level(self.level)
            return
        if self.state == "win":
            if k in ("return", "kp_enter"):
                if self.level < len(LEVELS) - 1:
                    self.start_level(self.level + 1)
                else:
                    self.show_menu("mode")
            return

        # --- playing ---
        if k == "h" and self.mode != 1:
            self.hint = not self.hint
            if self.hint:
                self.compute_hint()
        elif k == "e" and self.mode != 1:
            self.show_explored = not self.show_explored
            if self.show_explored:
                self.compute_hint()
        elif k == "space" and self.mode == 0:
            p = self.players[0]
            p.queue, p.auto = [], True
            self.hint = True
        elif k in ALL_MOVE_KEYS:
            for p in self.players:
                if not p.ai and k in p.keys:
                    p.auto, p.queue = False, []     # manual input cancels auto-solve
                    d = p.keys[k]
                    if d not in p.held:
                        p.held.append(d)
                    p.buffer = d

    def key_up(self, e):
        k = e.keysym.lower()
        if k in ALL_MOVE_KEYS:
            # delay the release a moment: X11 sends fake release+press pairs while a key repeats
            if k in self.pending:
                self.root.after_cancel(self.pending[k])
            self.pending[k] = self.root.after(30, lambda k=k: self.release(k))

    def release(self, k):
        self.pending.pop(k, None)
        for p in self.players:
            if k in p.keys and p.keys[k] in p.held:
                p.held.remove(p.keys[k])

    def focus_lost(self, _e=None):
        """If the window loses focus while a key is down we never get its release -> orb runs away."""
        for p in self.players:
            p.held.clear()
            p.buffer = None

    # ----- game loop -----
    def tick(self):
        if not self.alive:
            return
        now = time.time()
        dt = min(now - self.last, 0.05)
        self.last = now
        if self.state == "menu":
            self.draw_menu_orbs(now)
        elif self.state == "play":
            self.update(dt)
        if self.state == "win":
            self.update_confetti(dt)
        if self.state in ("play", "win"):
            self.draw_dynamic()
        self.root.after(16, self.tick)

    def update(self, dt):
        for p in self.players:
            self.update_player(p, dt)
            self.step_trail(p)
            if self.state != "play":
                break

    def step_trail(self, p):
        p.trail.append((p.bx, p.by))
        if p.target is None and len(p.trail) > 1:
            p.trail.pop(0)                          # tail shrinks when the orb rests
        while len(p.trail) > 10:
            p.trail.pop(0)

    def begin_move(self, p, cell):
        p.target = cell
        if self.t0 is None and not p.ai:
            self.t0 = time.time()

    def update_player(self, p, dt):
        if p.target is not None:
            tx, ty = p.target
            dx, dy = tx - p.bx, ty - p.by
            dist = math.hypot(dx, dy)
            step = p.speed * (1.3 if p.auto else 1.0) * dt
            if step < dist:
                p.bx += dx / dist * step
                p.by += dy / dist * step
                p.roll += (dx + dy) / dist * step / 0.31   # rolling: arc length / radius
                return
            p.roll += (dx + dy) / max(dist, 1e-9) * dist / 0.31
            p.bx, p.by = float(tx), float(ty)       # arrived
            p.cell, p.target = (tx, ty), None
            p.moves += 1
            if p is self.players[0] and (self.hint or self.show_explored):
                self.compute_hint()
            if p.cell == self.maze.goal:
                self.state = "win"
                self.winner = p
                self.t_end = time.time()
                p.auto = False
                self.spawn_confetti(p.color)
                for q in self.players:
                    q.trail = []
            return

        x, y = p.cell
        if p.ai or p.auto:
            if p.ai and self.t0 is None:
                return                              # CPU waits until the human starts
            if not p.queue:                         # A* from wherever the orb is now
                path, _ = astar(self.maze, p.cell, self.maze.goal)
                p.queue = path[1:]
            if p.queue:
                self.begin_move(p, p.queue.pop(0))
            else:
                p.auto = False
            return

        d = p.buffer or (p.held[-1] if p.held else None)
        p.buffer = None
        if d and d not in self.maze.walls[y][x]:
            dx, dy = DIRS[d]
            self.begin_move(p, (x + dx, y + dy))

    # ----- confetti -----
    def spawn_confetti(self, color):
        cols = [color, YEL, TEAL, PINK, ORG, BLUE, "#ffffff"]
        self.confetti = [[random.uniform(0, W), random.uniform(-H * .7, 0), random.uniform(-30, 30),
                          random.uniform(90, 220), random.choice(cols), random.uniform(4, 8),
                          random.uniform(0, 6.28), random.uniform(-6, 6)] for _ in range(70)]

    def update_confetti(self, dt):
        for c in self.confetti:
            c[0] += c[2] * dt + math.sin(c[6]) * 0.6
            c[1] += c[3] * dt
            c[6] += c[7] * dt
            if c[1] > H + 10:
                c[1], c[0] = -10, random.uniform(0, W)

    # ----- drawing -----
    def draw_ball(self, p):
        cv, cs = self.cv, self.cs
        x, y = self.cpx(p.bx, p.by)
        r = cs * 0.31
        n = len(p.trail)
        for i, (tx, ty) in enumerate(p.trail):      # comet tail
            if math.hypot(tx - p.bx, ty - p.by) < 0.12:
                continue
            f = (i + 1) / (n + 1)
            px, py = self.cpx(tx, ty)
            rr = r * (0.25 + 0.6 * f)
            cv.create_oval(px - rr, py - rr, px + rr, py + rr,
                           fill=tint(p.color, FLOOR, .10 + .32 * f), outline="", tags="dyn")
        for s, t in ((1.38, .16), (1.18, .34)):     # halo (kept inside the corridor)
            rr = r * s
            cv.create_oval(x - rr, y - rr, x + rr, y + rr, fill=tint(p.color, FLOOR, t),
                           outline="", tags="dyn")
        cv.create_oval(x - r + 1, y - r + 3, x + r + 1, y + r + 3, fill="#05040a", outline="", tags="dyn")
        ring = "#e6d9ff" if p.ai else mix(p.color, "#ffffff", .45)
        for i, (s, t) in enumerate(((1.0, 0.0), (0.9, 0.35), (0.76, 0.7), (0.6, 1.0), (0.44, 1.35))):
            col = tint(p.color, p.color2, t) if t <= 1 else tint("#ffffff", p.color, (t - 1) * .6)
            rr = r * s
            ox, oy = x - r * .07 * i, y - r * .09 * i
            cv.create_oval(ox - rr, oy - rr, ox + rr, oy + rr, fill=col,
                           outline=ring if i == 0 else "", width=max(2, cs // 14), tags="dyn")
        for k in (0, 1):                            # two crossing stripes show the rolling
            a = p.roll + k * math.pi / 2
            ex, ey = math.cos(a) * r * 0.78, math.sin(a) * r * 0.78
            cv.create_line(x - ex, y - ey, x + ex, y + ey, fill=tint(p.color2, p.color, .55),
                           width=max(2, cs // 14), capstyle="round", tags="dyn")
        cv.create_oval(x - r * .58, y - r * .64, x - r * .16, y - r * .26, fill="#fff6e0",
                       outline="", tags="dyn")
        cv.create_oval(x + r * .25, y + r * .35, x + r * .42, y + r * .5, fill=mix(p.color, "#ffffff", .5),
                       outline="", tags="dyn")

    def draw_goal(self):
        cv, cs = self.cv, self.cs
        gx, gy = self.cpx(*self.maze.goal)
        t = time.time()
        for k in range(3):                          # ripples spreading out of the target
            ph = (t * .9 + k / 3) % 1
            r = cs * (0.16 + 0.30 * ph)
            cv.create_oval(gx - r, gy - r, gx + r, gy + r, outline=tint(PINK, FLOOR, 1 - ph),
                           width=max(1, cs // 14), tags="dyn")
        pulse = 1 + 0.08 * math.sin(t * 5)
        for r, c in ((0.25, tint(PINK, FLOOR, .45)), (0.20, PINK), (0.12, YEL), (0.05, "#ffffff")):
            rr = cs * r * pulse
            cv.create_oval(gx - rr, gy - rr, gx + rr, gy + rr, fill=c, outline="", tags="dyn")
        for k in range(3):                          # tiny orbiting sparks
            a = t * 2.2 + k * 2.094
            sx, sy = gx + math.cos(a) * cs * .33, gy + math.sin(a) * cs * .33
            rr = max(1.5, cs * .04)
            cv.create_oval(sx - rr, sy - rr, sx + rr, sy + rr, fill=YEL if k else "#ffffff",
                           outline="", tags="dyn")

    def draw_dynamic(self):
        cv, cs = self.cv, self.cs
        cv.delete("dyn")
        now = time.time()
        t = 0.0 if self.t0 is None else (self.t_end or now) - self.t0
        p0 = self.players[0]
        big = F("display", 22)

        # header numbers
        if self.mode == 0:
            cv.create_text(60, 68, text=str(p0.moves), anchor="w", fill=p0.color, font=big, tags="dyn")
            info = f"A* path  {max(len(self.path) - 1, 0)} steps      explored  {len(self.explored)} cells"
        else:
            p1 = self.players[1]
            cv.create_text(60, 68, text=str(p0.moves), anchor="w", fill=p0.color, font=big, tags="dyn")
            cv.create_text(W - 60, 68, text=str(p1.moves), anchor="e", fill=p1.color, font=big, tags="dyn")
            lvl_name = LEVELS[self.level][0].title()
            info = (f"{lvl_name} race to the target" if self.mode == 1
                    else f"{lvl_name}      CPU {p1.speed:.1f} cells/s      A* path {max(len(self.path) - 1, 0)}")
        cv.create_text(W // 2, 68, text=f"{int(t // 60):02d}:{int(t % 60):02d}", fill=YEL, font=big, tags="dyn")
        cv.create_text(W // 2, 92, text=info, fill=MUTED, font=F("ui", 9, False), tags="dyn")

        if self.mode != 1 and self.show_explored:
            r = cs * 0.16
            col = tint(TEAL, FLOOR, .26)
            for (x, y) in self.explored:
                px, py = self.cpx(x, y)
                cv.create_oval(px - r, py - r, px + r, py + r, fill=col, outline="", tags="dyn")
        if self.mode != 1 and self.hint and len(self.path) > 1:
            pts = []
            for (x, y) in self.path:
                pts += list(self.cpx(x, y))
            cv.create_line(*pts, fill=tint(GREEN, FLOOR, .22), width=max(4, cs // 3),
                           capstyle="round", joinstyle="round", tags="dyn")
            cv.create_line(*pts, fill=GREEN, width=max(2, cs // 7), dash=(2, 4),
                           capstyle="round", joinstyle="round", tags="dyn")

        self.draw_goal()
        for p in self.players:
            self.draw_ball(p)

        if self.state == "win":
            self.draw_win(t)

    def draw_win(self, t):
        cv, cs = self.cv, self.cs
        w = self.winner
        size = cs * self.n
        for x, y, _, _, col, s, a, _ in self.confetti:      # confetti falls behind the card
            if not (self.ox + 4 < x < self.ox + size - 4 and self.oy + 4 < y < self.oy + size - 4):
                continue
            ca, sa = math.cos(a) * s, math.sin(a) * s
            cb, sb = -sa * .5, ca * .5
            cv.create_polygon(x + ca + cb, y + sa + sb, x + ca - cb, y + sa - sb,
                              x - ca - cb, y - sa - sb, x - ca + cb, y - sa + sb,
                              fill=col, outline="", tags="dyn")

        if self.mode == 0:
            title = "YOU ESCAPED!"
        elif self.mode == 1:
            title = f"{w.name} WINS!"
        else:
            title = "YOU WIN!" if not w.ai else "CPU (A*) WINS!"
        cy = self.oy + cs * self.n // 2
        glow_rrect(cv, 100, cy - 112, W - 100, cy + 112, 26, w.color, FLOOR,
                   layers=((16, .08), (10, .16), (5, .32)), tags="dyn")
        rrect(cv, 100, cy - 112, W - 100, cy + 112, 26, fill=PANEL, outline=w.color, width=3, tags="dyn")
        cv.create_text(W // 2 + 3, cy - 56 + 3, text=title, fill=tint(w.color, PANEL, .3),
                       font=F("display", 32), tags="dyn")
        cv.create_text(W // 2, cy - 56, text=title, fill=w.color, font=F("display", 32), tags="dyn")

        for (cx0, cx1, label, value) in ((132, 350, "Time", f"{t:.1f} s"), (370, 588, "Moves", str(w.moves))):
            rrect(cv, cx0, cy - 16, cx1, cy + 44, 14, fill=DARK, outline=LINE, width=2, tags="dyn")
            cv.create_text((cx0 + cx1) / 2, cy - 1, text=label, fill=MUTED, font=F("ui", 9, False), tags="dyn")
            cv.create_text((cx0 + cx1) / 2, cy + 23, text=value, fill=TEXT, font=F("display", 18), tags="dyn")

        nxt = "next level" if self.level < len(LEVELS) - 1 else "menu"
        self.draw_keys([("Enter", nxt), ("R", "replay"), ("M", "menu")], W // 2, cy + 82, "dyn")


if __name__ == "__main__":
    root = tk.Tk()
    Game(root)
    root.mainloop()
