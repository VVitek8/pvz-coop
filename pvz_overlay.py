# -*- coding: utf-8 -*-
"""
Draws the friend's mouse (arrow + "Name: plant in hand"), the seed slot he took and short messages on top of YOUR game window.
A transparent, click-through window that is shown ONLY while the game window itself is in the foreground.
The mapping game->screen is calibrated automatically from your own mouse (the game's own mouse coordinates vs. the Windows
cursor), so it does not depend on window size, DPI scaling or black bars. Works with windowed / borderless; exclusive
full screen hides it (Windows only, needs tkinter).
"""
import threading

GAME_W, GAME_H = 800.0, 600.0       # the game's logical screen


def fit_axis(pairs):
    """least squares screen = a*logical + b from [(logical, screen)]; None if the samples do not spread enough"""
    n = len(pairs)
    if n < 8:
        return None
    lo, hi = min(p[0] for p in pairs), max(p[0] for p in pairs)
    if hi - lo < 120:
        return None
    mx = sum(p[0] for p in pairs) / n
    my = sum(p[1] for p in pairs) / n
    var = sum((p[0] - mx) ** 2 for p in pairs)
    if var <= 0:
        return None
    a = sum((p[0] - mx) * (p[1] - my) for p in pairs) / var
    return a, my - a * mx


def letterbox(size):
    """800x600 centred in a (w, h) client area (keeps the aspect ratio) -> (ax, bx, ay, by)"""
    w, h = size
    s = min(w / GAME_W, h / GAME_H)
    return s, (w - GAME_W * s) / 2, s, (h - GAME_H * s) / 2


def stretch(size):
    w, h = size
    return w / GAME_W, 0.0, h / GAME_H, 0.0


class Mapper:
    """game logical coords -> coords inside the game's client area. fit: auto | letterbox | stretch"""
    def __init__(self, fit='auto'):
        self.fit, self.size = fit, None
        self.px, self.py, self.cal = [], [], None

    def reset(self, size):
        self.size, self.px, self.py, self.cal = size, [], [], None

    def sample(self, logical, rel):
        """logical = the game's mouse (x, y); rel = Windows cursor relative to the client area"""
        if self.fit != 'auto':
            return
        if self.px and abs(self.px[-1][0] - logical[0]) < 2 and abs(self.py[-1][0] - logical[1]) < 2:
            return
        self.px.append((logical[0], rel[0])); self.py.append((logical[1], rel[1]))
        del self.px[:-80], self.py[:-80]
        fx, fy = fit_axis(self.px), fit_axis(self.py)
        if fx and fy and 0.4 < fx[0] < 5 and 0.4 < fy[0] < 5:
            self.cal = (fx[0], fx[1], fy[0], fy[1])

    def coeffs(self):
        if self.cal:
            return self.cal
        return stretch(self.size) if self.fit == 'stretch' else letterbox(self.size)

    def map(self, x, y):
        ax, bx, ay, by = self.coeffs()
        return ax * x + bx, ay * y + by

    def scale(self):
        c = self.coeffs()
        return c[0], c[2]


class Overlay:
    def __init__(self, mem, cfg, log=print):
        self.mem, self.cfg, self.log = mem, cfg, log
        self.lock = threading.Lock()
        self.cursor, self.banner, self.rects, self.toasts, self.own = None, None, [], [], None
        self.alive = True
        self.thread = None

    def set(self, cursor=None, banner=None, rects=None, toasts=None, own=None):
        with self.lock:
            self.cursor, self.banner, self.rects, self.toasts, self.own = cursor, banner, rects or [], toasts or [], own

    def start(self):
        import tkinter  # noqa: F401  (fail early in the caller if tkinter is missing)
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()

    def stop(self):
        self.alive = False

    def _run(self):
        import ctypes
        import tkinter as tk
        from ctypes import wintypes
        key = '#010101'
        root = tk.Tk()
        root.overrideredirect(True)
        root.attributes('-topmost', True)
        root.attributes('-transparentcolor', key)
        root.configure(bg=key)
        canvas = tk.Canvas(root, bg=key, highlightthickness=0)
        canvas.pack(fill='both', expand=True)
        root.update_idletasks()
        user32 = ctypes.windll.user32
        try:                                              # click-through, never takes the focus from the game
            hwnd = user32.GetParent(root.winfo_id()) or root.winfo_id()
            ex = user32.GetWindowLongW(hwnd, -20)
            user32.SetWindowLongW(hwnd, -20, ex | 0x80000 | 0x20 | 0x08000000 | 0x80)
        except Exception as e:
            self.log('[overlay] click-through not available: %r' % (e,))
        color = self.cfg.get('color', '#ffa500')
        mapper = Mapper(self.cfg.get('fit', 'auto'))
        state = {'geo': None, 'shown': False}

        def hide():
            if state['shown']:
                root.withdraw()
                state['shown'] = False

        def text(x, y, s, fill, size=11, anchor='nw'):
            canvas.create_text(x + 1, y + 1, text=s, anchor=anchor, fill='black', font=('Arial', size, 'bold'))
            canvas.create_text(x, y, text=s, anchor=anchor, fill=fill, font=('Arial', size, 'bold'))

        def tick():
            if not self.alive:
                root.destroy()
                return
            try:
                rect = self.mem.client_rect() if self.mem.is_foreground() else None     # only while the game is in front
                with self.lock:
                    cur, banner, rects, toasts, own = self.cursor, self.banner, self.rects, self.toasts, self.own
                if not rect or not (cur or banner or rects or toasts):
                    hide()
                else:
                    size = (rect[2], rect[3])
                    if mapper.size != size:
                        mapper.reset(size)
                    pt = wintypes.POINT()
                    user32.GetCursorPos(ctypes.byref(pt))
                    rel = (pt.x - rect[0], pt.y - rect[1])
                    if own and 0 <= rel[0] < size[0] and 0 <= rel[1] < size[1]:
                        mapper.sample(own[:2], rel)
                    geo = '%dx%d+%d+%d' % (rect[2], rect[3], rect[0], rect[1])
                    if geo != state['geo']:
                        root.geometry(geo)
                        state['geo'] = geo
                    if not state['shown']:
                        root.deiconify()
                        state['shown'] = True
                    root.attributes('-topmost', True)
                    canvas.delete('all')
                    sx_, sy_ = mapper.scale()
                    for (x, y, w, h, label) in rects:           # the seed slot the friend took
                        x0, y0 = mapper.map(x, y)
                        canvas.create_rectangle(x0, y0, x0 + w * sx_, y0 + h * sy_, outline=color, width=3)
                        if label:
                            text(x0, y0 + h * sy_ + 2, label, color, 10)
                    if cur:
                        px, py = mapper.map(cur[0], cur[1])
                        canvas.create_polygon(px, py, px, py + 22, px + 6, py + 17, px + 11, py + 28, px + 15, py + 26,
                                              px + 10, py + 16, px + 17, py + 16, fill=color, outline='black', width=2)
                        if cur[2]:                              # the plant in the friend's hand, in a box next to his cursor
                            wbox = 9 * len(cur[2]) + 14
                            canvas.create_rectangle(px + 18, py + 22, px + 18 + wbox, py + 46, fill='#202020', outline=color, width=2)
                            canvas.create_text(px + 25, py + 34, text=cur[2], anchor='w', fill='#ffffff', font=('Arial', 12, 'bold'))
                    if self.cfg.get('debug_self') and own:       # calibration check: a cross where YOUR mouse should be
                        ox, oy = mapper.map(own[0], own[1])
                        canvas.create_line(ox - 8, oy, ox + 8, oy, fill='#00ff00', width=2)
                        canvas.create_line(ox, oy - 8, ox, oy + 8, fill='#00ff00', width=2)
                    if banner:
                        text(size[0] / 2, 30, banner, '#ffffff', 14, 'center')
                    for i, t in enumerate(toasts[-3:]):
                        text(size[0] / 2, 60 + 24 * i, t, color, 13, 'center')
            except Exception as e:
                self.log('[overlay] %r' % (e,))
            root.after(40, tick)
        hide()
        tick()
        root.mainloop()
