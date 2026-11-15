# -*- coding: utf-8 -*-
"""
PvZ online co-op, python side, v4.

Every player runs his own normal game (own zombies, own falling suns).  What is shared is set in coop_config.json
(see CONFIG.md):  plants, sun wallet, death, victory, level start, seed choice, the friend's mouse (overlay) ...
All sharing only happens while BOTH players are on the SAME level.  Different levels are allowed or not
("allow_different_levels").

Game side = PvZ_Coop.CT (00 CORE + 01A or 01B, optional 02 NO-PAUSE).  Hotkeys are read here:
    F6 menu      F7 resync lawn + sun to the host's      F8 disconnect

    python pvz_coop.py                  # idle, F6 in a level
    python pvz_coop.py --host           # start hosting right away
    python pvz_coop.py --join 26.1.2.3  # join right away (Radmin / Hamachi / LAN)
    python pvz_coop.py --pid 1234       # when two games run on one PC
"""
import argparse
import collections
import copy
import json
import os
import re
import socket
import struct
import sys
import threading
import time

# ------------------------------------------------------------------ shared buffer layout (must match the CT)
COOP_BASE = 0x00700600
OFF = dict(MODE=0x00, APPLYING=0x04, TICK=0x08, HEART=0x0C, MENUSHOW=0x1C, MENUDONE=0x20, MENURES=0x24, INMENU=0x28,
           IN_HEAD=0x38, IN_TAIL=0x3C, SAVEESP=0x4C, NOPAUSE=0x50, HOLD=0x54, HOLD_ZCD=0x58, HOLD_SUN=0x5C, QRES=0x60,
           IN=0x280, TITLE=0x880, PROMPT=0x8C0, BTN1=0x9C0, BTN2=0x9E0)
BUF_SIZE = 0xA00
IN_N = 32
ENTRY = struct.Struct('<8i')        # type, tick, row, col, p1, p2, v1, v2
# entries the game-side code knows
A_KILL_PLANT, A_ADD_PLANT, A_LOST, A_WIN = 2, 5, 6, 7
A_SEED_PICK, A_SEED_UNPICK, A_SEED_CLOSE = 8, 9, 10
Q_BOWL, Q_AWARD, Q_CAP = 0x0B, 0x0C, 0x0D       # queries: the answer appears in QRES
QNONE = 0xFFFFFFFF

MODE_OFF, MODE_HOST, MODE_CLIENT = 0, 1, 2
BTN1_RES, BTN2_RES = 0x3E8, 0x3E9
VK_F6, VK_F7, VK_F8 = 0x75, 0x76, 0x77

# ------------------------------------------------------------------ game structures (Cheat_Engine_addresses.txt)
PVZ_BASE, BOARD_OFF = 0x6A9EC0, 0x768
APP_MODE, APP_SCENE, APP_CHOOSER, APP_WM = 0x7F8, 0x7FC, 0x774, 0x320
WM_MOUSE_X, WM_MOUSE_Y = 0xE0, 0xE4
B_PLANT, B_PLANT_MAX, P_SIZE = 0xAC, 0xB0, 0x14C
B_CURSOR, B_LEVEL, B_SUN = 0x138, 0x5550, 0x5560
CUR_SLOT, CUR_SEED, CUR_IMI, CUR_TYPE = 0x24, 0x28, 0x2C, 0x30
CH_SEEDS, CH_STRIDE, CH_TYPE, CH_STATE, CH_START_BTN, N_SEEDS = 0xA4, 0x3C, 0x20, 0x24, 0x88, 49
BTN_DISABLED = 0x1A
B_ZCD, B_SUNCD, B_TICK, APP_INTERVAL = 0x559C, 0x5538, 0x5568, 0x454
B_SEEDBANK, SB_N, SB_FIRST, SB_STRIDE = 0x144, 0x24, 0x28, 0x50            # SeedBank object: slot count, first slot, slot size
SP_COOLED, SP_TOTAL, SP_TYPE, SP_IMI, SP_ACTIVE, SP_REFRESH = 0x24, 0x28, 0x34, 0x38, 0x48, 0x49
B_COINS, B_COINS_MAX, C_SIZE = 0xE4, 0xE8, 0xD8                            # items (coins, suns, trophy, ...)
C_X, C_Y, C_DEAD1, C_DEAD2, C_COLLECTED, C_TYPE = 0x24, 0x28, 0x38, 0x3C, 0x50, 0x58
OFFSCREEN = struct.pack('<ff', -2000.0, -2000.0)
SC_LOADING, SC_MENU, SC_INTRO, SC_PLAYING, SC_LOST, SC_AWARD = 0, 1, 2, 3, 4, 5
# plants that vanish by themselves right after doing their job: their disappearance is NOT sent to the friend
INSTANT_PLANTS = {2, 4, 11, 14, 15, 17, 19, 20, 27, 35}
IMITATER = 48
PLANT_NAMES = ['Peashooter', 'Sunflower', 'Cherry Bomb', 'Wall-nut', 'Potato Mine', 'Snow Pea', 'Chomper', 'Repeater',
               'Puff-shroom', 'Sun-shroom', 'Fume-shroom', 'Grave Buster', 'Hypno-shroom', 'Scaredy-shroom', 'Ice-shroom',
               'Doom-shroom', 'Lily Pad', 'Squash', 'Threepeater', 'Tangle Kelp', 'Jalapeno', 'Spikeweed', 'Torchwood',
               'Tall-nut', 'Sea-shroom', 'Plantern', 'Cactus', 'Blover', 'Split Pea', 'Starfruit', 'Pumpkin',
               'Magnet-shroom', 'Cabbage-pult', 'Flower Pot', 'Kernel-pult', 'Coffee Bean', 'Garlic', 'Umbrella Leaf',
               'Marigold', 'Melon-pult', 'Gatling Pea', 'Twin Sunflower', 'Gloom-shroom', 'Cattail', 'Winter Melon',
               'Gold Magnet', 'Spikerock', 'Cob Cannon', 'Imitater']

# ------------------------------------------------------------------ network protocol
PROTO_VER = 5
K_HELLO, K_ADD, K_REMOVE, K_SUN, K_SETSUN, K_PLANTS, K_REQ = 1, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15
K_STATE, K_CURSOR, K_SEEDS, K_SEEDREQ, K_SLOTS, K_SLOTUSE = 0x20, 0x21, 0x22, 0x23, 0x24, 0x25
K_LOSE, K_WIN = 0x30, 0x31
K_PING, K_PONG, K_BYE = 0x40, 0x41, 0x50
FRAME = struct.Struct('<HB')
P_HELLO = struct.Struct('<BB16s')
P_ADD = struct.Struct('<hhhh')      # row, col, type, imitater
P_REM = struct.Struct('<hhh')       # row, col, type
P_INT = struct.Struct('<i')         # sun delta / absolute sun
P_CNT = struct.Struct('<H')
P_STATE = struct.Struct('<bhhBBih')  # scene, mode, level, done, inboard, board tick, ms per tick
P_SLOTUSE = struct.Struct('<BhhH')   # slot index, seed type, imitater, recharge time
P_CURSOR = struct.Struct('<hhhhhh') # x, y, seed, imitater, cursor type, seed slot index
P_SEEDREQ = struct.Struct('<BB')    # seed, want(0/1)


def pack_frame(kind, payload=b''):
    return FRAME.pack(len(payload) + 1, kind) + payload


# ------------------------------------------------------------------ configuration
DEFAULTS = {
    'name': 'Player',
    'port': 7777,
    'notify': True,                      # "Player connected" box
    'peers_file': 'coop_peers.txt',
    'allow_different_levels': False,     # True: the friends may play different levels (nothing is shared then)
    'wait_for_partner_finish': True,     # client only (everybody waits for the host): finished first on a different level -> wait
    'reward_lock': True,                 # nobody can pick up the level reward until BOTH have finished (same level)
    'lawn_resync': 5.0,                  # seconds: the host re-sends its lawn so both lawns stay identical (0 = off)
    'time_tolerance': 25,                # game ticks of drift allowed before the client speeds up / slows down     # finished first on different levels -> wait until the friend finishes his level
    'no_pause': True,                    # the game keeps running while a pause/menu window is open (also needs script 02 for Esc/focus loss)
    'seed_choice': 'host',               # "host": only the host picks seeds | "both": either may pick | "off": everybody picks alone
    'lock_client_start': True,           # seed_choice=host: the client's "Let's Rock" button is disabled until the host starts
    'start_wait_max': 180,               # seconds a player may be held at the level start waiting for the friend
    'sync': {
        'plants': True,                  # plants appear / disappear on both lawns
        'sun': True,                     # one common sun wallet
        'death': True,                   # zombies reached the house for one -> for both
        'victory': True,                 # level completed for one -> completed for both
        'level_start': True,             # the CLIENT's first wave waits until the host is playing (the host never waits)
        'slots': True,                   # same seed slots (content) + recharge starts on both sides
        'time': True,                    # the client follows the host's game speed and clock
        'cursor': True,                  # see the friend's mouse and the plant in his hand
    },
    'overlay': {'enabled': True, 'send_hz': 20, 'color': '#ffa500', 'show_name': True,
                'fit': 'auto',            # auto: calibrated from your own mouse | letterbox | stretch (how 800x600 sits in the window)
                'debug_self': False},     # draws a green cross where YOUR mouse is: shows if the mapping is right
    'award_coin_types': [8, 16],         # item types treated as the level reward (8 trophy, 16 plant card)
    'no_plant_sync_modes': [],           # extra GameMode ids where plants are never synced (bowling is detected by the game itself)
    'strings': {},                       # override any text of the in-game menus, see CONFIG.md
    'lawnstrings_path': '',              # full path to LawnStrings.txt if it is not found automatically
    'debug': False,
    # timing (rarely touched)
    'poll_interval': 0.04, 'echo_ttl': 3.0, 'ready_delay': 1.5, 'max_sun_delta': 2000, 'dialog_guard': 6.0,
    'state_interval': 0.25,
}

STRINGS = {            # short, LawnStrings-like texts (the game's message box cuts long button captions)
    'TITLE': 'PvZ CO-OP', 'HOST': 'Host Game', 'JOIN': 'Join Game', 'OK': 'OK', 'KEEP': 'Keep', 'STOP': 'Stop',
    'RESYNC': 'Resync', 'DISCONNECT': 'Disconnect', 'CONNECT': 'Connect', 'NEXT': 'Next', 'AGAIN': 'Start over',
    'CANCEL': 'Cancel', 'STOPWAIT': 'Stop waiting',
}
NATIVE_KEY = re.compile(r'^\[[A-Z0-9_]+\]$')
# LawnStrings keys tried for every text (first one that exists in the game's LawnStrings.txt wins).
# COOP_* are our own keys: paste LawnStrings_coop_additions.txt into the game's LawnStrings.txt to use them.
LS_KEYS = {
    'TITLE': ['COOP_TITLE'], 'HOST': ['COOP_HOST'], 'JOIN': ['COOP_JOIN'], 'KEEP': ['COOP_KEEP'], 'STOP': ['COOP_STOP'],
    'RESYNC': ['COOP_RESYNC'], 'DISCONNECT': ['COOP_DISCONNECT'], 'CONNECT': ['COOP_CONNECT'], 'NEXT': ['COOP_NEXT'],
    'AGAIN': ['COOP_AGAIN'], 'STOPWAIT': ['COOP_STOPWAIT'],
    'OK': ['COOP_OK', 'DIALOG_BUTTON_OK'], 'CANCEL': ['COOP_CANCEL', 'DIALOG_BUTTON_CANCEL'],
}
LS_KEY_LINE = re.compile(r'^\[([A-Za-z0-9_]+)\]\s*$')


def load_lawnstrings(path):
    """set of keys defined in LawnStrings.txt ("[KEY]" on its own line, text below it); empty set if unreadable"""
    keys = set()
    try:
        with open(path, encoding='utf-8-sig', errors='ignore') as f:
            for line in f:
                m = LS_KEY_LINE.match(line.strip())
                if m:
                    keys.add(m.group(1))
    except OSError:
        pass
    return keys


def merge_cfg(base, over):
    res = copy.deepcopy(base)
    for k, v in (over or {}).items():
        if isinstance(v, dict) and isinstance(res.get(k), dict):
            res[k] = merge_cfg(res[k], v)
        else:
            res[k] = v
    return res


def normalize_cfg(cfg):
    """accepts v3 style flat keys (sync_plants / sync_sun) and a few spelling variants"""
    cfg = dict(cfg or {})
    sync = dict(cfg.get('sync') or {})
    for old, new in (('sync_plants', 'plants'), ('sync_sun', 'sun')):
        if old in cfg:
            sync.setdefault(new, cfg.pop(old))
    if sync:
        cfg['sync'] = sync
    return cfg


# ------------------------------------------------------------------ choosing the game process (two windows on one PC)
def find_game_pids(names):
    import pymem.process
    want = [n.lower() for n in names]
    res = []
    for p in pymem.process.list_processes():
        exe = p.szExeFile.decode('utf-8', 'ignore') if isinstance(p.szExeFile, bytes) else p.szExeFile
        if exe.lower() in want:
            res.append((p.th32ProcessID, exe))
    return res


def foreground_pid():
    try:
        import ctypes
        user32 = ctypes.windll.user32
        pid = ctypes.c_ulong(0)
        user32.GetWindowThreadProcessId(user32.GetForegroundWindow(), ctypes.byref(pid))
        return pid.value
    except Exception:
        return 0


def pick_pid(cands, fg_fn=foreground_pid, ask_fn=input, wait=12.0, log=print, sleep=time.sleep):
    """One game -> it. Several games -> the one whose window you click within `wait` seconds, else ask for a PID."""
    if len(cands) == 1:
        return cands[0][0]
    pids = [p for p, _ in cands]
    log('[coop] %d PvZ processes found: PIDs %s' % (len(pids), ', '.join(map(str, pids))))
    log('[coop] >>> CLICK THE GAME WINDOW this script must control (you have %d s) <<<' % wait)
    t0 = time.time()
    while time.time() - t0 < wait:
        fg = fg_fn()
        if fg in pids:
            log('[coop] using the game you clicked: PID %d' % fg)
            return fg
        sleep(0.1)
    ans = ask_fn('Type the PID of the game to control (Task Manager -> Details -> PID): ').strip()
    if not ans.isdigit() or int(ans) not in pids:
        raise RuntimeError('PID %r is not one of %s' % (ans, pids))
    return int(ans)


# ------------------------------------------------------------------ memory access
class Mem:
    def read(self, addr, n): raise NotImplementedError
    def write(self, addr, data): raise NotImplementedError
    def u32(self, a): return struct.unpack('<I', self.read(a, 4))[0]
    def i32(self, a): return struct.unpack('<i', self.read(a, 4))[0]
    def u8(self, a): return self.read(a, 1)[0]
    def w32(self, a, v): self.write(a, struct.pack('<I', v & 0xFFFFFFFF))
    def keys_down(self): return set()          # VK codes pressed while the game window is focused
    def client_rect(self): return None         # (left, top, width, height) of the game's client area on the screen
    def is_foreground(self): return True       # is the game window the active window?
    def press_enter(self): return False        # sends Enter to the game window (closes the "waiting" box)
    def game_dir(self): return None            # folder of the game's exe


class PymemMem(Mem):
    def __init__(self, names=("PlantsVsZombies_insert.exe", "PlantsVsZombies.exe"), pid=None):
        import pymem
        if pid is None:
            cands = find_game_pids(names)
            if not cands:
                raise RuntimeError("PvZ process not found (%s). Start the game first." % ", ".join(names))
            pid = pick_pid(cands)
        self.pm = pymem.Pymem()
        self.pm.open_process_from_id(int(pid))
        self.name = "pid %d" % int(pid)
        self._hwnd = None
        try:
            import ctypes
            from ctypes import wintypes
            self.ctypes, self.wintypes = ctypes, wintypes
            self.user32 = ctypes.windll.user32
        except Exception:
            self.user32 = None

    def read(self, addr, n): return self.pm.read_bytes(addr, n)
    def write(self, addr, data): self.pm.write_bytes(addr, bytes(data), len(data))

    def keys_down(self):
        if not self.user32:
            return set()
        try:
            pid = self.ctypes.c_ulong(0)
            self.user32.GetWindowThreadProcessId(self.user32.GetForegroundWindow(), self.ctypes.byref(pid))
            if pid.value != self.pm.process_id:
                return set()
            return {vk for vk in (VK_F6, VK_F7, VK_F8) if self.user32.GetAsyncKeyState(vk) & 0x8000}
        except Exception:
            return set()

    def is_foreground(self):
        if not self.user32:
            return True
        try:
            pid = self.ctypes.c_ulong(0)
            self.user32.GetWindowThreadProcessId(self.user32.GetForegroundWindow(), self.ctypes.byref(pid))
            return pid.value == self.pm.process_id
        except Exception:
            return True

    def hwnd(self):
        if not self.user32:
            return None
        if self._hwnd and self.user32.IsWindow(self._hwnd):
            return self._hwnd
        ct, wt = self.ctypes, self.wintypes
        found = []
        Enum = ct.WINFUNCTYPE(wt.BOOL, wt.HWND, wt.LPARAM)

        def cb(h, _):
            p = wt.DWORD(0)
            self.user32.GetWindowThreadProcessId(h, ct.byref(p))
            if p.value == self.pm.process_id and self.user32.IsWindowVisible(h):
                r = wt.RECT()
                self.user32.GetClientRect(h, ct.byref(r))
                found.append(((r.right - r.left) * (r.bottom - r.top), h))
            return True
        self.user32.EnumWindows(Enum(cb), 0)
        self._hwnd = max(found)[1] if found else None
        return self._hwnd

    def client_rect(self):
        h = self.hwnd()
        if not h or self.user32.IsIconic(h):
            return None
        ct, wt = self.ctypes, self.wintypes
        r, pt = wt.RECT(), wt.POINT(0, 0)
        self.user32.GetClientRect(h, ct.byref(r))
        self.user32.ClientToScreen(h, ct.byref(pt))
        return (pt.x, pt.y, r.right - r.left, r.bottom - r.top)

    def game_dir(self):
        try:
            ct, wt = self.ctypes, self.wintypes
            buf = ct.create_unicode_buffer(1024)
            n = wt.DWORD(1024)
            ct.windll.kernel32.QueryFullProcessImageNameW(self.pm.process_handle, 0, buf, ct.byref(n))
            return os.path.dirname(buf.value) or None
        except Exception:
            return None

    def press_enter(self):
        h = self.hwnd()
        if not h:
            return False
        for msg, lp in ((0x100, 0x001C0001), (0x102, 0x001C0001), (0x101, 0xC01C0001)):     # KEYDOWN, CHAR, KEYUP
            self.user32.PostMessageW(h, msg, 0x0D, lp)
        return True


# ------------------------------------------------------------------ TCP link
class Link:
    def __init__(self, sock, rx):
        self.sock, self.rx, self.alive = sock, rx, True
        self.lock = threading.Lock()
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        threading.Thread(target=self._reader, daemon=True).start()

    def send(self, kind, payload=b''):
        if not self.alive:
            return False
        try:
            with self.lock:
                self.sock.sendall(pack_frame(kind, payload))
            return True
        except OSError:
            self.close()
            return False

    def _recv_exact(self, n):
        buf = b''
        while len(buf) < n:
            chunk = self.sock.recv(n - len(buf))
            if not chunk:
                raise OSError('closed')
            buf += chunk
        return buf

    def _reader(self):
        try:
            while self.alive:
                ln, kind = FRAME.unpack(self._recv_exact(FRAME.size))
                payload = self._recv_exact(ln - 1) if ln > 1 else b''
                self.rx.append((self, kind, payload))
        except OSError:
            pass
        finally:
            self.close()
            self.rx.append((self, None, b''))

    def close(self):
        if self.alive:
            self.alive = False
            for f in (lambda: self.sock.shutdown(socket.SHUT_RDWR), self.sock.close):
                try:
                    f()
                except OSError:
                    pass


class NullOverlay:
    def set(self, cursor=None, banner=None, rects=None, toasts=None, own=None): pass
    def stop(self): pass


def level_text(key):
    if not key:
        return '-'
    mode, lvl = key
    if mode == 0 and lvl > 0:
        return 'level %d-%d' % ((lvl - 1) // 10 + 1, (lvl - 1) % 10 + 1)
    return 'mode %d' % mode


# ------------------------------------------------------------------ the co-op engine
class Coop:
    def __init__(self, mem, cfg=None, log=print, overlay=None):
        self.mem = mem
        self.cfg = merge_cfg(DEFAULTS, normalize_cfg(cfg))
        self.log = log
        self.overlay = overlay or NullOverlay()
        self.rx = collections.deque()
        self.link = None
        self.role = MODE_OFF
        self.peer_name = '?'
        self.server = None
        self.pending_in = collections.deque()
        self.notices = collections.deque()
        self.stop = False
        self.ping_ms = None
        self._last_ping = 0.0
        self._last_poll = 0.0
        self._prev_keys = set()
        self.last_heart = (0, time.time())
        self.initial_at = None
        self.in_dialog = False
        self.want_wait = False
        self.local = dict(scene=-1, key=None, inboard=False, tick=0, interval=10)
        self.peer = None
        self.peer_cursor = None
        self._state_sent = None
        self._state_t = 0.0
        self._cursor_sent = None
        self._cursor_t = 0.0
        self._was_same = False
        self.prev_scene = None
        self.ls_keys = None
        self.reset_tracking()

    # ---- helpers
    def find_lawnstrings(self):
        """read the game's LawnStrings.txt once (unpacked game: <game dir>/properties/LawnStrings.txt)"""
        if self.ls_keys is not None:
            return
        self.ls_keys = set()
        cands = [self.cfg.get('lawnstrings_path')]
        d = self.mem.game_dir()
        if d:
            cands += [os.path.join(d, 'properties', 'LawnStrings.txt'), os.path.join(d, 'LawnStrings.txt')]
        for p in cands:
            if p and os.path.exists(p):
                self.ls_keys = load_lawnstrings(p)
                used = sorted(k for ks in LS_KEYS.values() for k in ks if k in self.ls_keys)
                self.log('[coop] LawnStrings: %s (%d keys); our texts taken from it: %s' % (p, len(self.ls_keys), ', '.join(used) or 'none, using the texts from the code'))
                return
        self.log('[coop] LawnStrings.txt not found (packed game?) - menu texts come from the code. Set "lawnstrings_path" in the config to use it.')

    def S(self, key):
        if key in self.cfg['strings']:
            return self.cfg['strings'][key]
        for k in LS_KEYS.get(key, ()):
            if self.ls_keys and k in self.ls_keys:
                return '[%s]' % k
        return STRINGS.get(key, key)

    def connected(self):
        return bool(self.link and self.link.alive)

    def sy(self, name):
        return bool(self.cfg['sync'].get(name))

    def dbg(self, msg):
        if self.cfg['debug']:
            self.log('[coop:debug] ' + msg)

    def reset_tracking(self):
        self.cur_board = 0
        self.board_since = 0.0
        self.prev = None            # {(idx, id): (row, col, type, imi)} of the plants seen last poll
        self.sun_prev = None
        self.expect_add, self.expect_rm = {}, {}
        self.bowling = None
        self.q = None               # outstanding query (kind, since)
        self.done_local = False
        self.award_seen0 = False
        self._award_t = 0.0
        self.win_from_remote = False
        self.lose_from_remote = False
        self.chooser_open = False
        self.seed_prev = None
        self.seed_expect = {}
        self.seed_cap = None
        self.seed_hold_until = 0.0
        self.seed_next = 0.0
        self.seed_sent = None
        self.seed_sent_t = 0.0
        self.seed_last_bank = frozenset()
        self.host_bank = None
        self.host_seed_done = False
        self.host_done_t = 0.0
        self.holding = False
        self.hold_since = None
        self.hold_given_up = False
        self.banner = None
        self.toasts = []
        self.own_mouse = None
        self.born = {}
        self.start_locked = False
        self.late_t = 0.0
        self._slot_t = 0.0
        self.slot_sent = None
        self.slot_prev = None
        self.slot_applied = False
        self.hidden = {}
        self.interval_orig = None
        self._lawn_t = 0.0

    # ---- shared buffer helpers
    def rd(self, k): return self.mem.u32(COOP_BASE + OFF[k])
    def wr(self, k, v): self.mem.w32(COOP_BASE + OFF[k], v)

    def check_buffer(self):
        self.find_lawnstrings()
        raw = self.mem.read(COOP_BASE, BUF_SIZE)
        if any(raw[0x80:0xA00]) and self.rd('MODE') == 0 and self.rd('HEART') == 0:
            self.log('[coop] WARNING: shared buffer %08X is not empty - another script may use it. '
                     'Change COOP_BASE / the define() block if the game misbehaves.' % COOP_BASE)
        for k in ('IN_HEAD', 'IN_TAIL', 'MENUSHOW', 'MENUDONE', 'HOLD'):
            self.wr(k, 0)
        self.wr('NOPAUSE', 1 if self.cfg['no_pause'] else 0)
        self.wr('QRES', QNONE)

    # ---- game state readers
    def app(self):
        try:
            return self.mem.u32(PVZ_BASE)
        except Exception:
            return 0

    def board(self):
        try:
            app = self.mem.u32(PVZ_BASE)
            return self.mem.u32(app + BOARD_OFF) if app else 0
        except Exception:
            return 0

    def game_mode(self):
        try:
            return self.mem.u32(self.mem.u32(PVZ_BASE) + APP_MODE)
        except Exception:
            return -1

    def scene(self):
        try:
            return self.mem.i32(self.mem.u32(PVZ_BASE) + APP_SCENE)
        except Exception:
            return -1

    def level_key(self, b):
        try:
            mode = self.mem.i32(self.mem.u32(PVZ_BASE) + APP_MODE)
            lvl = self.mem.i32(b + B_LEVEL) if (b and mode == 0) else 0
            return (mode, lvl)
        except Exception:
            return None

    def pump_alive(self):
        h = self.rd('HEART')
        now = time.time()
        if h != self.last_heart[0]:
            self.last_heart = (h, now)
        return now - self.last_heart[1] < 1.0

    # ---- IN ring (python -> game)
    def in_push(self, entry):
        head, tail = self.rd('IN_HEAD'), self.rd('IN_TAIL')
        nxt = (head + 1) % IN_N
        if nxt == tail:
            return False
        self.mem.write(COOP_BASE + OFF['IN'] + head * 32, ENTRY.pack(*entry))
        self.wr('IN_HEAD', nxt)
        return True

    def queue_in(self, entry):
        self.pending_in.append(tuple(entry))

    def query(self, kind, max_age=2.0):
        """non-blocking: returns the answer of the game (int) or None while it is still being asked"""
        now = time.time()
        if self.q is None:
            self.wr('QRES', QNONE)
            self.queue_in((kind, 0, 0, 0, 0, 0, 0, 0))
            self.q = (kind, now)
            return None
        k, t = self.q
        if k != kind:
            return None
        v = self.rd('QRES')
        if v != QNONE:
            self.q = None
            return v
        if now - t > max_age:
            self.q = None                                   # pump did not answer (not running / MODE 0): ask again later
        return None

    # ---- level / cursor readers
    def read_sun(self, b=None):
        b = b or self.board()
        return self.mem.i32(b + B_SUN) if b else 0

    def read_plants(self, b=None):
        """{(slot, id): (row, col, type, imitater)} of every living plant"""
        b = b or self.board()
        if not b:
            return {}
        arr, mx = self.mem.u32(b + B_PLANT), self.mem.u32(b + B_PLANT_MAX)
        if not arr or mx == 0 or mx > 2048:
            return {}
        raw = self.mem.read(arr, mx * P_SIZE)
        res = {}
        for i in range(mx):
            o = i * P_SIZE
            if struct.unpack_from('<I', raw, o + 4)[0] != b or raw[o + 0x141] or raw[o + 0x142]:
                continue
            row, typ, col, imi, pid = (struct.unpack_from('<i', raw, o + 0x1C)[0], struct.unpack_from('<i', raw, o + 0x24)[0],
                                       struct.unpack_from('<i', raw, o + 0x28)[0], struct.unpack_from('<i', raw, o + 0x138)[0],
                                       struct.unpack_from('<I', raw, o + 0x148)[0])
            res[(i, pid)] = (row, col, typ, imi)
        return res

    def read_cursor(self, b):
        try:
            wm = self.mem.u32(self.mem.u32(PVZ_BASE) + APP_WM)
            x, y = self.mem.i32(wm + WM_MOUSE_X), self.mem.i32(wm + WM_MOUSE_Y)
        except Exception:
            return None
        seed, imi, ctype, slot = -1, -1, 0, -1
        try:
            co = self.mem.u32(b + B_CURSOR) if b else 0
            if co:
                ctype = self.mem.i32(co + CUR_TYPE)
                if ctype in (1, 2, 3):
                    seed, imi = self.mem.i32(co + CUR_SEED), self.mem.i32(co + CUR_IMI)
                    slot = self.mem.i32(co + CUR_SLOT) if ctype == 1 else -1
                    if not 0 <= seed <= IMITATER:
                        seed = -1
        except Exception:
            pass
        return (max(-32000, min(32000, x)), max(-32000, min(32000, y)), seed, imi, ctype, max(-1, min(slot, 100)))

    def read_chooser(self):
        """(chooser ptr, bank set, states list) of the open seed chooser, or None. Validated: entry i must be seed type i."""
        try:
            ch = self.mem.u32(self.mem.u32(PVZ_BASE) + APP_CHOOSER)
            if not ch:
                return None
            raw = self.mem.read(ch + CH_SEEDS, N_SEEDS * CH_STRIDE)
        except Exception:
            return None
        states = []
        for i in range(N_SEEDS):
            o = i * CH_STRIDE
            if struct.unpack_from('<I', raw, o + CH_TYPE)[0] != i:
                return None
            states.append(struct.unpack_from('<I', raw, o + CH_STATE)[0])
        return ch, frozenset(i for i, s in enumerate(states) if s in (0, 1)), states

    # ---- connection management
    def local_ips(self):
        ips = set()
        try:
            for ai in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
                ips.add(ai[4][0])
        except OSError:
            pass
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.connect(('10.255.255.255', 1)); ips.add(s.getsockname()[0]); s.close()
        except OSError:
            pass
        return sorted(i for i in ips if not i.startswith('127.'))

    def start_host(self):
        if self.server:
            return True
        try:
            srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            srv.bind(('0.0.0.0', self.cfg['port'])); srv.listen(1); srv.settimeout(0.5)
        except OSError as e:
            self.log('[coop] cannot listen: %s' % e)
            return False
        self.server = srv
        threading.Thread(target=self._accept_loop, daemon=True).start()
        self.log('[coop] hosting on port %d (%s)' % (self.cfg['port'], ', '.join(self.local_ips())))
        return True

    def stop_host(self):
        if self.server:
            try:
                self.server.close()
            except OSError:
                pass
            self.server = None

    def _accept_loop(self):
        srv = self.server
        while self.server is srv and srv:
            try:
                s, addr = srv.accept()
            except socket.timeout:
                continue
            except OSError:
                return
            if self.link and self.link.alive:
                s.close(); continue
            link = Link(s, self.rx)
            link.send(K_HELLO, P_HELLO.pack(PROTO_VER, MODE_HOST, self.cfg['name'].encode('ascii', 'replace')[:16]))

    def join(self, host, port=None, timeout=5.0):
        port = port or self.cfg['port']
        try:
            s = socket.create_connection((host, port), timeout=timeout)
            s.settimeout(None)
        except OSError as e:
            self.log('[coop] connect failed: %s' % e)
            return False
        link = Link(s, self.rx)
        link.send(K_HELLO, P_HELLO.pack(PROTO_VER, MODE_CLIENT, self.cfg['name'].encode('ascii', 'replace')[:16]))
        return True

    def disconnect(self, notify_peer=True):
        if self.link:
            if notify_peer:
                self.link.send(K_BYE)
            self.link.close()
        self._lost()

    def _lost(self):
        self.restore_interval()
        self.link = None
        self.role = MODE_OFF
        self.peer = None
        self.peer_cursor = None
        self.wr('MODE', MODE_OFF)
        self.wr('HOLD', 0)
        self.holding = False
        self.pending_in.clear()
        self.initial_at = None
        self._was_same = False
        self.overlay.set(None, None)

    # ---- protocol handling
    def _on_connected(self, link, role_of_peer, name):
        self.link, self.peer_name = link, name
        self.role = MODE_CLIENT if role_of_peer == MODE_HOST else MODE_HOST
        if self.role == MODE_HOST:
            self.stop_host()
        self.prev = None
        self.sun_prev = None
        self.peer = None
        self._state_sent = None
        self._was_same = False
        self.expect_add, self.expect_rm = {}, {}
        self.wr('MODE', self.role)
        self.log('[coop] connected: I am %s, peer = %s' % ('HOST' if self.role == MODE_HOST else 'CLIENT', name))
        self.notices.append('Player "%s" connected. You are the %s.' % (name, 'HOST' if self.role == MODE_HOST else 'CLIENT'))
        self.send_state(force=True)

    def _handle(self, link, kind, payload):
        if kind is None:
            if link is self.link:
                self.log('[coop] peer disconnected')
                self.notices.append('Co-op connection closed.')
                self._lost()
            return
        if kind == K_HELLO:
            ver, role, name = P_HELLO.unpack(payload)
            if ver != PROTO_VER:
                self.log('[coop] protocol version mismatch (%d != %d): both players need the same pvz_coop.py' % (ver, PROTO_VER))
                link.close(); return
            if link is not self.link:
                self._on_connected(link, role, name.split(b'\0')[0].decode('ascii', 'replace'))
            return
        if link is not self.link:
            return
        if kind == K_STATE:
            sc, mode, lvl, done, inb, tick, itv = P_STATE.unpack(payload)
            self.peer = dict(scene=sc, key=(mode, lvl) if inb else None, done=bool(done), inboard=bool(inb), t=time.time(),
                             tick=tick, interval=itv)
        elif kind == K_ADD:
            self.remote_add(*P_ADD.unpack(payload))
        elif kind == K_REMOVE:
            self.remote_remove(*P_REM.unpack(payload))
        elif kind == K_SUN:
            self.remote_sun_delta(P_INT.unpack(payload)[0])
        elif kind == K_SETSUN:
            self.remote_set_sun(P_INT.unpack(payload)[0])
        elif kind == K_PLANTS and self.role == MODE_CLIENT:
            self.remote_plant_list(payload)
        elif kind == K_REQ and self.role == MODE_HOST:
            self.send_lawn()
        elif kind == K_CURSOR:
            old = self.peer_cursor
            self.peer_cursor = P_CURSOR.unpack(payload) + (time.time(),)
            if self.peer_cursor[2] >= 0 and (old is None or old[2] != self.peer_cursor[2]):
                nm = PLANT_NAMES[self.peer_cursor[2]] if self.peer_cursor[2] < len(PLANT_NAMES) else 'a plant'
                self.add_toast('%s took %s' % (self.peer_name, nm))
        elif kind == K_SLOTS:
            self.remote_slots(payload)
        elif kind == K_SLOTUSE:
            self.remote_slot_use(*P_SLOTUSE.unpack(payload))
        elif kind == K_SEEDS:
            self.remote_seeds(payload)
        elif kind == K_SEEDREQ:
            self.remote_seed_req(*P_SEEDREQ.unpack(payload))
        elif kind == K_LOSE:
            self.remote_lose()
        elif kind == K_WIN:
            self.remote_win()
        elif kind == K_PING:
            link.send(K_PONG, payload)
        elif kind == K_PONG:
            self.ping_ms = (time.time() - struct.unpack('<d', payload)[0]) * 1000.0
        elif kind == K_BYE:
            link.close()

    # ---- same level?
    def same_level(self):
        p = self.peer
        if not (self.connected() and p):
            return False
        if time.time() - p['t'] > 4.0:
            return False
        me = self.local
        return bool(me['inboard'] and p['inboard'] and me['key'] is not None and me['key'] == p['key'])

    def plants_enabled(self):
        if not (self.sy('plants') and self.same_level()):
            return False
        if self.bowling is not False:                      # unknown yet (still asking the game) or a bowling level
            return False
        return self.game_mode() not in self.cfg['no_plant_sync_modes']

    def sun_enabled(self):
        return self.sy('sun') and self.same_level()

    # ---- applying what the friend did
    def remote_add(self, row, col, typ, imi):
        b = self.board()
        if not b or not self.plants_enabled():
            return
        key = (row, col, typ)
        if any((r, c, t) == key for (r, c, t, _) in self.read_plants(b).values()):
            return                                            # we already have this plant there (both planted at once)
        self.expect_add[key] = time.time()
        self.queue_in((A_ADD_PLANT, 0, row, col, typ, imi if typ == IMITATER else -1, 0, 0))

    def remote_remove(self, row, col, typ):
        b = self.board()
        if not b or not self.plants_enabled():
            return
        key = (row, col, typ)
        if any((r, c, t) == key for (r, c, t, _) in self.read_plants(b).values()):
            self.expect_rm[key] = time.time()
            self.queue_in((A_KILL_PLANT, 0, row, col, typ, 0, 0, 0))

    def remote_sun_delta(self, d):
        b = self.board()
        if not b or not self.sun_enabled() or self.sun_prev is None or abs(d) > self.cfg['max_sun_delta']:
            return
        cur = self.read_sun(b)
        new = max(0, cur + d)
        self.mem.w32(b + B_SUN, new)
        self.sun_prev += new - cur                            # not echoed back; our own unsent change stays visible

    def remote_set_sun(self, v):
        b = self.board()
        if not b or not self.sun_enabled():
            return
        self.mem.w32(b + B_SUN, max(0, v))
        self.sun_prev = max(0, v)

    def remote_plant_list(self, payload):
        """resync: make my lawn equal to the host's"""
        b = self.board()
        if not b or not self.plants_enabled():
            return
        n = P_CNT.unpack_from(payload, 0)[0]
        host = set()
        host_imi = {}
        for i in range(n):
            row, col, typ, imi = P_ADD.unpack_from(payload, P_CNT.size + i * P_ADD.size)
            host.add((row, col, typ)); host_imi[(row, col, typ)] = imi
        mine = {(r, c, t) for (r, c, t, _) in self.read_plants(b).values()}
        for key in host - mine:
            self.remote_add(key[0], key[1], key[2], host_imi[key])
        now = time.time()
        for key in mine - host:
            if now - self.born.get(key, 0.0) > 2.0:              # not a plant I planted a moment ago (host does not know it yet)
                self.remote_remove(*key)

    def remote_lose(self):
        if not (self.sy('death') and self.same_level()) or self.local['scene'] != SC_PLAYING:
            return
        self.lose_from_remote = True
        self.log('[coop] %s lost the level -> you lose too' % self.peer_name)
        self.queue_in((A_LOST, 0, 0, 0, 0, 0, 0, 0))

    def remote_win(self):
        if not (self.sy('victory') and self.same_level()) or self.cfg['reward_lock'] or self.local['scene'] != SC_PLAYING or self.done_local:
            return
        self.win_from_remote = True
        self.done_local = True
        self.log('[coop] %s completed the level -> you complete it too' % self.peer_name)
        self.queue_in((A_WIN, 0, 0, 0, 0, 0, 0, 0))

    def send_lawn(self, sun=True):
        """host -> client: all my plants and my sun"""
        b = self.board()
        if not (self.connected() and b and self.same_level()):
            return
        ps = sorted(set((r, c, t, i) for (r, c, t, i) in self.read_plants(b).values()))[:500]
        if self.plants_enabled():
            self.link.send(K_PLANTS, P_CNT.pack(len(ps)) + b''.join(P_ADD.pack(*p) for p in ps))
        if sun and self.sun_enabled():
            self.link.send(K_SETSUN, P_INT.pack(self.read_sun(b)))

    # ---- state exchange / overlay
    def send_state(self, force=False):
        if not self.connected():
            return
        me = self.local
        mode, lvl = me['key'] if me['key'] else (0, 0)
        payload = P_STATE.pack(max(-1, min(me['scene'], 100)), max(-32000, min(mode, 32000)), max(-32000, min(lvl, 32000)),
                               1 if self.done_local else 0, 1 if me['inboard'] else 0, me['tick'], me['interval'])
        now = time.time()
        if force or now - self._state_t >= self.cfg['state_interval'] or (self._state_sent and payload[:7] != self._state_sent[:7]):
            self._state_sent, self._state_t = payload, now
            self.link.send(K_STATE, payload)

    def cursor_label(self, c):
        x, y, seed, imi, ctype = c[:5]
        if seed >= 0:
            nm = PLANT_NAMES[seed] if seed < len(PLANT_NAMES) else 'plant %d' % seed
            if seed == IMITATER and 0 <= imi < len(PLANT_NAMES):
                nm = 'Imitater (%s)' % PLANT_NAMES[imi]
        elif ctype not in (0,):
            nm = 'tool'
        else:
            nm = ''
        who = self.peer_name if self.cfg['overlay'].get('show_name', True) else ''
        return (who + (': ' if who and nm else '') + nm).strip()

    def add_toast(self, text, secs=2.5):
        self.toasts.append((text, time.time() + secs))
        del self.toasts[:-4]

    def slot_rect(self, b, idx):
        """(x, y, w, h) of seed slot idx on MY board (logical coords), or None"""
        try:
            bank = self.mem.u32(b + B_SEEDBANK)
            n = self.mem.u32(bank + SB_N) if bank else 0
            if not (0 <= idx < n <= 10):
                return None
            o = bank + SB_FIRST + idx * SB_STRIDE
            return tuple(self.mem.i32(o + k) for k in (0x08, 0x0C, 0x10, 0x14))
        except Exception:
            return None

    def update_overlay(self, now):
        ov = self.cfg['overlay']
        cur = None
        pc = self.peer_cursor
        rects = []
        if ov.get('enabled') and self.sy('cursor') and self.connected() and pc and now - pc[6] < 1.5 \
                and self.peer and self.peer['inboard'] and self.local['inboard']:
            cur = (pc[0], pc[1], self.cursor_label(pc))
            if pc[2] >= 0 and pc[5] >= 0:                               # the friend holds a plant taken from slot pc[5]
                r = self.slot_rect(self.cur_board, pc[5])
                if r:
                    rects.append(r + (self.peer_name if ov.get('show_name', True) else '',))
        self.toasts = [t for t in self.toasts if t[1] > now]
        try:
            self.overlay.set(cur, self.banner, rects, [t[0] for t in self.toasts], self.own_mouse)
        except TypeError:                                              # an overlay that only knows (cursor, banner)
            self.overlay.set(cur, self.banner)

    def poll_cursor(self, now, b):
        if not (self.sy('cursor') and self.connected()):
            return
        if now - self._cursor_t < 1.0 / max(1, self.cfg['overlay'].get('send_hz', 20)):
            return
        c = self.read_cursor(b)
        if c is None:
            return
        self.own_mouse = (c[0], c[1])
        if c != self._cursor_sent or now - self._cursor_t > 0.5:
            self._cursor_sent, self._cursor_t = c, now
            self.link.send(K_CURSOR, P_CURSOR.pack(*c))

    # ---- scene events: death, victory, level start
    def poll_scene(self, now):
        sc = self.local['scene']
        if sc != self.prev_scene:
            self.dbg('scene %r -> %r (level %s)' % (self.prev_scene, sc, level_text(self.local['key'])))
            if sc == SC_LOST and self.prev_scene is not None:
                if self.lose_from_remote:
                    self.lose_from_remote = False
                elif self.sy('death') and self.same_level() and self.connected():
                    self.log('[coop] you lost the level -> %s loses too' % self.peer_name)
                    self.link.send(K_LOSE)
            self.prev_scene = sc

    def poll_award(self, now):
        """did the level just get completed? (HasLevelAwardDropped, asked from the game)"""
        if not self.connected() or self.local['scene'] != SC_PLAYING or self.done_local and not self.q:
            return
        if not (self.sy('victory') or self.cfg['wait_for_partner_finish'] or self.cfg['reward_lock']):
            return
        if self.q is None and now - self._award_t < 0.25:
            return
        r = self.query(Q_AWARD)
        if self.q is None and r is None:
            self._award_t = now
        if r is None:
            return
        self._award_t = now
        if r == 0:
            self.award_seen0 = True
        elif self.award_seen0 and not self.done_local:
            self.done_local = True
            self.send_state(force=True)
            self.log('[coop] level completed')
            rl = self.cfg['reward_lock']
            if self.sy('victory') and self.same_level() and not rl:
                self.link.send(K_WIN)
            elif self.cfg['wait_for_partner_finish'] and self.role == MODE_CLIENT and self.peer and self.peer['inboard'] \
                    and not self.peer['done'] and not (rl and self.same_level()):
                self.want_wait = True

    def update_hold(self, now, b):
        """level start: the first wave (and the falling suns) wait until both players are playing"""
        want, text = False, None
        me, p = self.local, self.peer
        playing = me['scene'] == SC_PLAYING
        if self.sy('level_start') and self.role == MODE_CLIENT and self.connected() and playing and p and now - p['t'] < 4.0 and not self.hold_given_up:
            allow = self.cfg['allow_different_levels']
            if p['inboard'] and p['key'] == me['key']:
                if p['scene'] not in (SC_PLAYING, SC_LOST, SC_AWARD):
                    want, text = True, 'Waiting for %s to start the level...' % self.peer_name
            elif not allow:
                want = True
                text = ('%s is on %s - go to %s' % (self.peer_name, level_text(p['key']), level_text(me['key']))
                        if p['inboard'] else 'Waiting for %s to start %s...' % (self.peer_name, level_text(me['key'])))
        if want:
            if self.hold_since is None:
                self.hold_since = now
            elif now - self.hold_since > self.cfg['start_wait_max']:
                self.hold_given_up = True
                self.log('[coop] waited %d s for %s - going on alone' % (self.cfg['start_wait_max'], self.peer_name))
                want = False
        else:
            self.hold_since = None
        if want and not self.holding:
            try:
                self.wr('HOLD_ZCD', self.mem.u32(b + B_ZCD))
                self.wr('HOLD_SUN', self.mem.u32(b + B_SUNCD))
                self.wr('HOLD', 1)
                self.holding = True
                self.log('[coop] level start is held: ' + text)
            except Exception as e:
                self.log('[coop] hold failed: %r' % (e,))
        elif not want and self.holding:
            self.wr('HOLD', 0)
            self.holding = False
            self.log('[coop] level start released')
        if want:
            self.banner = text
        elif me['scene'] in (SC_INTRO, SC_PLAYING) and self.connected() and p and now - p['t'] < 4.0 \
                and p['inboard'] and p['key'] != me['key'] and not self.cfg['allow_different_levels']:
            self.banner = '%s is on %s (you: %s) - nothing is shared until you are on the same level' % (
                self.peer_name, level_text(p['key']), level_text(me['key']))
        else:
            self.banner = None

    # ---- reward lock: the level reward stays out of reach until the friend has finished too
    def read_coins(self, b):
        arr, mx = self.mem.u32(b + B_COINS), self.mem.u32(b + B_COINS_MAX)
        if not arr or mx == 0 or mx > 4096:
            return []
        raw = self.mem.read(arr, mx * C_SIZE)
        res = []
        for i in range(mx):
            o = i * C_SIZE
            if struct.unpack_from('<I', raw, o + 4)[0] != b or raw[o + C_DEAD1] or raw[o + C_DEAD2] or raw[o + C_COLLECTED]:
                continue
            res.append((arr + o, struct.unpack_from('<i', raw, o + C_TYPE)[0], raw[o + C_X:o + C_X + 8 + 0]))
        return res

    def poll_reward_lock(self, now, b):
        p = self.peer
        lock = bool(self.cfg['reward_lock'] and self.connected() and self.same_level() and self.done_local and p
                    and not p['done'] and self.local['scene'] == SC_PLAYING)
        if not lock and not self.hidden:
            return
        types = set(self.cfg['award_coin_types'])
        try:
            coins = {a: (t, pos) for a, t, pos in self.read_coins(b)}
        except Exception:
            return
        if lock:
            for a, (t, pos) in coins.items():
                if t in types:
                    if a not in self.hidden:
                        self.hidden[a] = self.mem.read(a + C_X, 8)
                    self.mem.write(a + C_X, OFFSCREEN)
            self.banner = 'Waiting for %s to finish the level - the reward unlocks then' % self.peer_name
        else:
            for a, pos in list(self.hidden.items()):
                if a in coins:
                    self.mem.write(a + C_X, pos)
                del self.hidden[a]
            self.log('[coop] reward unlocked')
            self.add_toast('Reward unlocked - take it!')

    # ---- game speed / clock: the client follows the host
    def restore_interval(self):
        if self.interval_orig is not None:
            try:
                self.mem.w32(self.mem.u32(PVZ_BASE) + APP_INTERVAL, self.interval_orig)
            except Exception:
                pass
            self.interval_orig = None

    def poll_time(self, now, b):
        p = self.peer
        if not (self.sy('time') and self.role == MODE_CLIENT and self.same_level() and p and self.local['scene'] == SC_PLAYING
                and p['scene'] == SC_PLAYING and p['interval'] > 0):
            self.restore_interval()
            return
        try:
            est = p['tick'] + (now - p['t']) * 1000.0 / p['interval']
            diff = self.local['tick'] - est                      # > 0: I am ahead of the host
            host_itv = max(2, min(p['interval'], 50))
            if abs(diff) < self.cfg['time_tolerance']:
                target = host_itv
            else:
                target = min(50, host_itv + 2) if diff > 0 else max(2, host_itv - 2)
            app = self.mem.u32(PVZ_BASE)
            cur = self.mem.i32(app + APP_INTERVAL)
            if cur != target:
                if self.interval_orig is None:
                    self.interval_orig = cur
                self.mem.w32(app + APP_INTERVAL, target)
        except Exception as e:
            self.dbg('time sync: %r' % (e,))

    # ---- seed slots (the bank on the board): content from the host, recharge on both sides
    def read_slots(self, b):
        bank = self.mem.u32(b + B_SEEDBANK)
        if not bank:
            return None, []
        n = self.mem.u32(bank + SB_N)
        if not 0 < n <= 10:
            return None, []
        raw = self.mem.read(bank + SB_FIRST, n * SB_STRIDE)
        slots = []
        for i in range(n):
            o = i * SB_STRIDE
            typ, imi = struct.unpack_from('<ii', raw, o + SP_TYPE)
            slots.append((typ, imi, raw[o + SP_REFRESH]))
        return bank, slots

    def poll_slots(self, now, b):
        if not (self.sy('slots') and self.connected() and self.same_level() and self.local['scene'] == SC_PLAYING):
            self.slot_prev = None
            return
        bank, slots = self.read_slots(b)
        if bank is None:
            return
        types = [(t, i) for t, i, _ in slots]
        if self.role == MODE_HOST and (types != self.slot_sent or now - self._slot_t > 2.0):
            self.slot_sent, self._slot_t = types, now
            self.link.send(K_SLOTS, bytes([len(types)]) + b''.join(struct.pack('<hh', t, i) for t, i in types))
        ref = [r for _, _, r in slots]
        if self.slot_prev is not None and len(self.slot_prev) == len(ref):
            for i, (was, is_) in enumerate(zip(self.slot_prev, ref)):
                if not was and is_:                              # this slot started recharging: tell the friend
                    total = self.mem.i32(bank + SB_FIRST + i * SB_STRIDE + SP_TOTAL)
                    self.link.send(K_SLOTUSE, P_SLOTUSE.pack(i, slots[i][0], slots[i][1], max(0, min(total, 65000))))
        self.slot_prev = ref

    def remote_slots(self, payload):
        """host -> client: make my slots hold the same plants"""
        b = self.board()
        if self.role != MODE_CLIENT or not b or not self.sy('slots') or not self.same_level():
            return
        n = payload[0]
        host = [struct.unpack_from('<hh', payload, 1 + 4 * k) for k in range(n)]
        bank, mine = self.read_slots(b)
        if bank is None:
            return
        if len(mine) != n:
            if not self.slot_applied:
                self.log('[coop] WARNING: the host has %d slots, you have %d - slots cannot be matched' % (n, len(mine)))
                self.slot_applied = True
            return
        for i, ((t, im), (mt, mi, _)) in enumerate(zip(host, mine)):
            if (t, im) != (mt, mi):
                o = bank + SB_FIRST + i * SB_STRIDE
                self.mem.write(o + SP_TYPE, struct.pack('<ii', t, im))
                self.dbg('slot %d: %d -> %d' % (i, mt, t))

    def remote_slot_use(self, idx, typ, imi, total):
        b = self.board()
        if not b or not self.sy('slots') or not self.same_level():
            return
        bank, slots = self.read_slots(b)
        if bank is None:
            return
        cand = [idx] if idx < len(slots) and slots[idx][0] == typ else [i for i, s_ in enumerate(slots) if s_[0] == typ]
        for i in cand:
            if not slots[i][2]:
                o = bank + SB_FIRST + i * SB_STRIDE
                self.mem.w32(o + SP_COOLED, 0)
                self.mem.w32(o + SP_TOTAL, total)
                self.mem.write(o + SP_ACTIVE, b'\x00')
                self.mem.write(o + SP_REFRESH, b'\x01')
                if self.slot_prev is not None and i < len(self.slot_prev):
                    self.slot_prev[i] = 1                        # do not echo it back
                break

    # ---- seed chooser
    def seed_capacity(self):
        if self.seed_cap is None:
            r = self.query(Q_CAP)
            if r is not None and 0 < r < 20:
                self.seed_cap = r
        return self.seed_cap

    def remote_seeds(self, payload):
        if self.role != MODE_CLIENT or self.cfg['seed_choice'] == 'off':
            return
        done, n = payload[0], payload[1]
        self.host_bank = frozenset(payload[2:2 + n])
        if done:
            self.host_seed_done = True
            self.host_done_t = time.time()

    def remote_seed_req(self, t, want):
        """host, seed_choice=both: apply what the client clicked"""
        if self.role != MODE_HOST or self.cfg['seed_choice'] != 'both' or not self.chooser_open or not self.same_level():
            return
        info = self.read_chooser()
        if info is None or not 0 <= t < N_SEEDS:
            return
        _, bank, states = info
        if want and states[t] == 3 and len(bank) < (self.seed_capacity() or 0):
            self.queue_in((A_SEED_PICK, 0, 0, 0, t, 0, 0, 0))
        elif not want and states[t] == 1:
            self.queue_in((A_SEED_UNPICK, 0, 0, 0, t, 0, 0, 0))

    def poll_seeds(self, now):
        mode = self.cfg['seed_choice']
        info = self.read_chooser() if self.local['scene'] == SC_INTRO else None
        was_open = self.chooser_open
        self.chooser_open = info is not None
        if mode not in ('host', 'both') or not self.connected():
            return
        if info is not None and not was_open:
            self.seed_prev, self.seed_expect, self.seed_cap, self.seed_hold_until = None, {}, None, 0.0
            self.seed_sent, self.seed_next = None, 0.0
            self.dbg('seed chooser opened')
        if info is None:
            if was_open and self.role == MODE_HOST and self.same_level():
                self.link.send(K_SEEDS, bytes([1, len(self.seed_last_bank)]) + bytes(sorted(self.seed_last_bank)))
                self.dbg('seed chooser closed on the host: START sent')
            elif self.role == MODE_HOST and self.same_level() and self.local['scene'] == SC_PLAYING and self.peer \
                    and self.peer['scene'] == SC_INTRO and now - self.late_t > 1.0:
                # the friend joined late: he is still choosing seeds while I already play -> tell him my slots, he starts with them
                self.late_t = now
                b = self.board()
                _, slots = self.read_slots(b) if b else (None, [])
                bank_types = sorted({t for t, _, _ in slots if 0 <= t < N_SEEDS})
                if bank_types:
                    self.link.send(K_SEEDS, bytes([1, len(bank_types)]) + bytes(bank_types))
                    self.dbg('late join: sent my slots %r' % bank_types)
            return
        ch, bank, states = info
        if not self.same_level():
            self.unlock_start(ch, bank)
            return
        self.seed_capacity()                                       # ask the game how many slots there are (both roles)
        if self.role == MODE_HOST:
            self.seed_last_bank = bank
            if bank != self.seed_sent or now - self.seed_sent_t > 1.0:
                self.seed_sent, self.seed_sent_t = bank, now
                self.link.send(K_SEEDS, bytes([0, len(bank)]) + bytes(sorted(bank)))
            return
        # ---- client
        if self.seed_prev is None:
            self.seed_prev = bank
        else:
            for t in sorted(bank ^ self.seed_prev):
                want = t in bank
                exp = self.seed_expect.get(t)
                if exp and exp[0] == want and now - exp[1] < 3.0:
                    self.seed_expect.pop(t)
                    continue
                if mode == 'both':                                  # my own click: ask the host
                    self.link.send(K_SEEDREQ, P_SEEDREQ.pack(t, 1 if want else 0))
                    self.seed_hold_until = now + 1.0
            self.seed_prev = bank
        if mode == 'host' and self.cfg['lock_client_start'] and not self.host_seed_done:
            self.lock_start_button(ch)
        else:
            self.unlock_start(ch, bank)
        if self.host_bank is not None and now >= self.seed_hold_until and now >= self.seed_next:
            cap = self.seed_capacity()
            if cap:
                for t in sorted(self.host_bank - bank):
                    if states[t] == 3 and len(bank) < cap:
                        self.seed_expect[t] = (True, now)
                        self.queue_in((A_SEED_PICK, 0, 0, 0, t, 0, 0, 0)); self.seed_next = now + 0.12
                        break
                else:
                    for t in sorted(bank - self.host_bank):
                        if states[t] == 1:
                            self.seed_expect[t] = (False, now)
                            self.queue_in((A_SEED_UNPICK, 0, 0, 0, t, 0, 0, 0)); self.seed_next = now + 0.12
                            break
        if self.host_seed_done and (bank == self.host_bank or now - self.host_done_t > 2.5):
            self.host_seed_done = False
            self.dbg('host started: closing my seed chooser')
            self.queue_in((A_SEED_CLOSE, 0, 0, 0, 0, 0, 0, 0))

    def lock_start_button(self, ch):
        try:
            btn = self.mem.u32(ch + CH_START_BTN)
            if btn > 0x10000 and self.mem.u8(btn + BTN_DISABLED) == 0:
                self.mem.write(btn + BTN_DISABLED, b'\x01')
                self.start_locked = True
        except Exception:
            pass

    def unlock_start(self, ch, bank):
        """give the Start button back (only if the bank is full: the game itself keeps it disabled otherwise)"""
        if not self.start_locked:
            return
        cap = self.seed_cap
        try:
            btn = self.mem.u32(ch + CH_START_BTN)
            if btn > 0x10000 and cap and len(bank) >= cap:
                self.mem.write(btn + BTN_DISABLED, b'\x00')
        except Exception:
            pass
        self.start_locked = False

    # ---- watching my own lawn and wallet
    def refresh_local(self, b):
        tick, itv = 0, 10
        try:
            if b:
                tick = self.mem.i32(b + B_TICK)
            itv = self.mem.i32(self.mem.u32(PVZ_BASE) + APP_INTERVAL)
        except Exception:
            pass
        self.local = dict(scene=self.scene(), key=self.level_key(b) if b else None, inboard=bool(b), tick=tick,
                          interval=itv if 0 < itv < 1000 else 10)

    def new_level(self, now, b):
        try:
            self.wr('HOLD', 0)                                  # ALWAYS: a stale hold would freeze the next level's first wave
        except Exception:
            pass
        self.restore_interval()
        self.reset_tracking()
        self.cur_board = b
        self.board_since = now if b else 0.0
        self.prev_scene = None
        self.holding = False
        self.dbg('new level / board %08X (%s)' % (b, level_text(self.local['key'])))

    def poll(self):
        now = time.time()
        b = self.board()
        self.refresh_local(b)
        sc = self.local['scene']
        entering_intro = b and sc == SC_INTRO and self.prev_scene not in (None, SC_INTRO)
        if b != self.cur_board or entering_intro:             # new level / left the level
            self.new_level(now, b)
            self.send_state(force=True)
            self.update_overlay(now)
            return
        if self.connected():
            self.send_state()
            rising = self.same_level()
            if rising and not self._was_same and self.role == MODE_HOST:
                self.initial_at = now + 0.3                       # same level now: host sends its lawn + sun
            self._was_same = rising
        if not b:
            self.update_overlay(now)
            return
        if self.connected():
            self.poll_scene(now)
            self.poll_seeds(now)
            self.poll_award(now)
            self.update_hold(now, b)
            self.poll_slots(now, b)
            self.poll_time(now, b)
            self.poll_reward_lock(now, b)
            self.poll_cursor(now, b)
            if self.bowling is None and self.same_level() and self.sy('plants'):
                r = self.query(Q_BOWL)
                if r is not None:
                    self.bowling = bool(r)
                    self.dbg('bowling level: %s' % self.bowling)
        else:
            self.banner = None
        if self.plants_enabled():
            cur = self.read_plants(b)
            if self.prev is None:
                self.prev = cur
            else:
                self.diff_plants(cur, now)
        else:
            self.prev = None
        ready = now - self.board_since >= self.cfg['ready_delay']
        sun = self.read_sun(b)
        if not ready:
            self.sun_prev = None
        elif not self.sun_enabled():
            self.sun_prev = sun                                   # follow silently: no jump when sharing starts
        elif self.sun_prev is None:
            self.sun_prev = sun
            if self.role == MODE_HOST and self.connected():
                self.link.send(K_SETSUN, P_INT.pack(sun))         # level just started: align the wallet
        elif sun != self.sun_prev:
            d = sun - self.sun_prev
            self.sun_prev = sun
            if self.connected() and abs(d) <= self.cfg['max_sun_delta']:
                self.link.send(K_SUN, P_INT.pack(d))
        for table in (self.expect_add, self.expect_rm):
            for k in [k for k, t in table.items() if now - t > self.cfg['echo_ttl']]:
                del table[k]
        self.update_overlay(now)

    def diff_plants(self, cur, now):
        ttl = self.cfg['echo_ttl']
        for pid, (row, col, typ, imi) in cur.items():
            if pid in self.prev:
                continue
            key = (row, col, typ)
            self.born[key] = now
            t = self.expect_add.pop(key, None)
            if t is not None and now - t < ttl:
                continue                                      # this is the plant WE just built for the friend
            if self.connected():
                self.link.send(K_ADD, P_ADD.pack(row, col, typ, imi))
        for pid, (row, col, typ, imi) in self.prev.items():
            if pid in cur:
                continue
            key = (row, col, typ)
            t = self.expect_rm.pop(key, None)
            if t is not None and now - t < ttl:
                continue                                      # we removed it because the friend lost it
            if typ in INSTANT_PLANTS:
                continue                                      # it left by itself (bomb exploded, ...): friend's copy does the same
            if self.connected():
                self.link.send(K_REMOVE, P_REM.pack(row, col, typ))
        self.prev = cur

    # ---- main loop
    def service(self):
        """everything that must keep running while a dialog is open"""
        now = time.time()
        while self.rx:
            link, kind, payload = self.rx.popleft()
            try:
                self._handle(link, kind, payload)
            except Exception as e:
                self.log('[coop] bad packet kind=%r: %s' % (kind, e))
        if now - self._last_poll >= self.cfg['poll_interval']:
            self._last_poll = now
            try:
                self.poll()
            except Exception as e:
                self.log('[coop] poll error: %r' % (e,))
        while self.pending_in and self.in_push(self.pending_in[0]):
            self.pending_in.popleft()
        if self.connected():
            if self.initial_at and now >= self.initial_at and self.board():
                self.initial_at = None
                self.send_lawn()
            rs = self.cfg['lawn_resync']
            if rs and self.role == MODE_HOST and now - self._lawn_t >= rs and self.local['scene'] == SC_PLAYING and self.board():
                self._lawn_t = now
                self.send_lawn(sun=False)                         # keep both lawns identical (no overlapping plants)
            if now - self._last_ping > 5:
                self._last_ping = now
                self.link.send(K_PING, struct.pack('<d', now))

    def step(self):
        self.service()
        self.poll_keys()
        if self.want_wait and not self.in_dialog:
            self.want_wait = False
            self.wait_dialog()
        if self.notices and self.cfg['notify'] and self.board() and self.pump_alive() and not self.in_dialog:
            self.dialog(self.S('TITLE'), self.notices.popleft(), self.S('OK'), self.S('OK'))

    def run(self):
        self.check_buffer()
        self.log('[coop] ready. In a level: F6 = menu, F7 = resync, F8 = disconnect')
        while not self.stop:
            try:
                self.step()
            except Exception as e:
                self.log('[coop] error: %r' % (e,))
            time.sleep(0.01)

    # ---- hotkeys / in-game menu
    def poll_keys(self):
        down = self.mem.keys_down()
        for vk in sorted(down - self._prev_keys):
            if vk == VK_F6:
                self.menu()
            elif vk == VK_F7:
                self.resync()
            elif vk == VK_F8:
                self.disconnect()
                self.log('[coop] disconnected (F8)')
        self._prev_keys = down

    def resync(self):
        if self.role == MODE_HOST:
            self.send_lawn()
        elif self.role == MODE_CLIENT and self.link:
            self.link.send(K_REQ)

    def wait_dialog(self):
        """finished a level before the friend did (different levels): wait until he finishes his"""
        name = self.peer_name

        def finished():
            p = self.peer
            return (not self.connected()) or p is None or p['done'] or not p['inboard']
        self.log('[coop] waiting for %s to finish his level' % name)
        self.dialog(self.S('TITLE'), 'Level complete. Waiting for %s to finish his level...' % name,
                    self.S('STOPWAIT'), self.S('STOPWAIT'), until=finished)

    def _text(self, text, size, key_ok=False):
        if key_ok and NATIVE_KEY.match(text or ''):
            data = text.encode('ascii')                         # a real LawnStrings key, e.g. [DIALOG_BUTTON_OK]
        else:
            data = (text or '').encode('ascii', 'replace').replace(b'[', b'(').replace(b']', b')')
        data = data[:size - 1]
        return data + b'\0' * (size - len(data))

    def dialog(self, title, prompt, b1, b2, timeout=None, until=None):
        """Show the game's own modal message box; returns 1 / 2 for button 1 / 2, 0 if the game could not show it.
        Network, polling and the game's IN ring keep running while it is open."""
        if not self.board():
            self.log('[coop] menu works only inside a level (no board found)')
            return 0
        self.in_dialog = True
        try:
            for key, text, size, ok in (('TITLE', title, 64, True), ('PROMPT', prompt, 256, False), ('BTN1', b1, 32, True), ('BTN2', b2, 32, True)):
                self.mem.write(COOP_BASE + OFF[key], self._text(text, size, ok))
            self.wr('MENUDONE', 0)
            self.wr('MENUSHOW', 1)
            t0 = time.time()
            warned, enter_t = False, None
            while not self.stop:
                if self.rd('MENUDONE') == 1:
                    res = self.rd('MENURES')
                    self.wr('MENUDONE', 0)
                    return 1 if res == BTN1_RES else 2
                self.service()
                if until and enter_t is None and until():
                    enter_t = time.time()
                    self.mem.press_enter()
                if enter_t and time.time() - enter_t > 3.0 and not warned:
                    warned = True
                    self.log('[coop] the friend is done - close the box with its button')
                if until is None:
                    if self.rd('MENUSHOW') == 1 and time.time() - t0 > self.cfg['dialog_guard']:
                        self.wr('MENUSHOW', 0)
                        self.log('[coop] the game did not show the menu: pump hook (01A/01B) is not running. '
                                 'Is it enabled? Is another script overwriting 415D40 / 415DF0? Try the other pump variant.')
                        return 0
                    if not warned and time.time() - t0 > 2.0 and self.rd('MENUSHOW') == 1:
                        warned = True
                        self.log('[coop] waiting for the game (go to a level)...')
                elif self.rd('MENUSHOW') == 1 and time.time() - t0 > self.cfg['dialog_guard']:
                    self.wr('MENUSHOW', 0)
                    return 0
                if timeout and time.time() - t0 > timeout:
                    self.wr('MENUSHOW', 0)
                    return 0
                time.sleep(0.02)
            return 0
        finally:
            self.in_dialog = False

    def peers_paths(self):
        p = self.cfg['peers_file']
        here = os.path.dirname(os.path.abspath(__file__))
        out = []
        for base in (p, os.path.join(here, os.path.basename(p))):
            for cand in (base, base + '.txt'):                 # Windows may have saved it as coop_peers.txt.txt
                if cand not in out:
                    out.append(cand)
        return out

    def load_peers(self):
        peers = []
        for path in self.peers_paths():
            if not os.path.exists(path):
                continue
            for line in open(path, encoding='utf-8', errors='ignore'):
                line = line.split('#')[0].strip()
                if not line:
                    continue
                parts = line.split(None, 1)
                host, _, port = parts[0].partition(':')
                try:
                    peers.append((parts[1] if len(parts) > 1 else parts[0], host, int(port) if port else self.cfg['port']))
                except ValueError:
                    self.log('[coop] bad line in %s: %r' % (path, line))
            self.log('[coop] read %d host(s) from %s' % (len(peers), path))
            break
        if not any(h == '127.0.0.1' for _, h, _ in peers):
            peers.append(('This PC (127.0.0.1)', '127.0.0.1', self.cfg['port']))   # two games on one computer
        return peers

    def status_text(self):
        if self.connected():
            ping = ('%d ms' % self.ping_ms) if self.ping_ms is not None else '-'
            same = 'same level' if self.same_level() else 'different levels'
            return 'Connected to %s as %s. Ping %s. %s.' % (self.peer_name, 'HOST' if self.role == MODE_HOST else 'CLIENT', ping, same)
        if self.server:
            return 'Hosting on %s:%d - waiting for a player.' % (', '.join(self.local_ips()) or '?', self.cfg['port'])
        return 'Offline.'

    def menu(self):
        S = self.S
        if self.connected():
            r = self.dialog(S('TITLE'), self.status_text(), S('RESYNC'), S('DISCONNECT'))
            if r == 1:
                self.resync()
            elif r == 2:
                self.disconnect()
            return
        r = self.dialog(S('TITLE'), self.status_text() + ' Host a game or join a friend?', S('HOST'), S('JOIN'))
        if r == 1:
            if self.start_host():
                r2 = self.dialog(S('TITLE'), 'Hosting on %s port %d. Tell your friend to join, then press Keep.' % (
                    ', '.join(self.local_ips()) or '?', self.cfg['port']), S('KEEP'), S('STOP'))
                if r2 == 2:
                    self.stop_host()
            else:
                self.dialog(S('TITLE'), 'Cannot listen on port %d (already in use?).' % self.cfg['port'], S('OK'), S('OK'))
        elif r == 2:
            peers = self.load_peers()
            if not peers:
                self.dialog(S('TITLE'), 'No hosts known. Put "ip[:port] name" lines into %s or run: pvz_coop.py --join IP' % self.cfg['peers_file'], S('OK'), S('OK'))
                return
            while True:
                for i, (name, host, port) in enumerate(peers):
                    rr = self.dialog(S('TITLE'), 'Join %s (%s:%d)? [%d/%d]' % (name, host, port, i + 1, len(peers)), S('CONNECT'), S('NEXT'))
                    if rr == 0:
                        return
                    if rr == 1:
                        if not self.join(host, port):
                            self.dialog(S('TITLE'), 'Could not connect to %s:%d' % (host, port), S('OK'), S('OK'))
                        return
                if self.dialog(S('TITLE'), 'End of the list.', S('AGAIN'), S('CANCEL')) != 1:
                    return


# ------------------------------------------------------------------ cli
def load_cfg(path='coop_config.json'):
    here = os.path.dirname(os.path.abspath(__file__))
    for p in (path, os.path.join(here, os.path.basename(path))):
        if os.path.exists(p):
            try:
                with open(p, encoding='utf-8-sig') as f:
                    cfg = json.load(f)
                return {k: v for k, v in cfg.items() if not k.startswith('_')}
            except Exception as e:
                print('bad %s: %s (using defaults)' % (p, e))
    return {}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--host', action='store_true', help='start hosting immediately')
    ap.add_argument('--join', metavar='IP[:PORT]', help='connect immediately')
    ap.add_argument('--port', type=int)
    ap.add_argument('--name')
    ap.add_argument('--process', help='game exe name (default PlantsVsZombies_insert.exe)')
    ap.add_argument('--pid', type=int, help='PID of the game to control (needed only when two games are running)')
    ap.add_argument('--config', default='coop_config.json')
    ap.add_argument('--no-overlay', action='store_true', help="do not draw the friend's mouse")
    ap.add_argument('--debug', action='store_true')
    a = ap.parse_args()
    cfg = load_cfg(a.config)
    if a.port: cfg['port'] = a.port
    if a.name: cfg['name'] = a.name
    if a.debug: cfg['debug'] = True
    names = (a.process,) if a.process else ("PlantsVsZombies_insert.exe", "PlantsVsZombies.exe")
    mem = PymemMem(names, a.pid)
    print('[coop] attached to', mem.name)
    overlay = None
    full = merge_cfg(DEFAULTS, normalize_cfg(cfg))
    if full['overlay'].get('enabled') and full['sync'].get('cursor') and not a.no_overlay:
        try:
            from pvz_overlay import Overlay
            overlay = Overlay(mem, full['overlay'], log=print)
            overlay.start()
        except Exception as e:
            print("[coop] mouse overlay is not available (%r) - the game itself is not affected" % (e,))
    coop = Coop(mem, cfg, overlay=overlay)
    if a.host:
        coop.start_host()
    if a.join:
        host, _, port = a.join.partition(':')
        coop.join(host, int(port) if port else coop.cfg['port'])
    try:
        coop.run()
    except KeyboardInterrupt:
        coop.disconnect()
        coop.wr('MODE', MODE_OFF)
        coop.wr('HOLD', 0)
        if overlay:
            overlay.stop()


if __name__ == '__main__':
    main()
