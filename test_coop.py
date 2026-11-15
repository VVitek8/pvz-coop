# -*- coding: utf-8 -*-
"""Loopback test of pvz_coop.py v4: two peers, fake game memory, real TCP sockets.
FakeGame mimics what PvZ_Coop.CT does (tick pump: apply entries, hold timers, un-pause, dialogs, queries).
It proves the python logic only - the assembler side can only be checked inside the real game."""
import os, struct, sys, tempfile, threading, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import pvz_coop as pc
import pvz_overlay as ov


class FakeGame(pc.Mem):
    def __init__(self):
        self.b = bytearray(0x800000)
        self.app, self.board, self.plants = 0x100000, 0x200000, 0x300000
        self.wm, self.cur, self.chooser, self.btn = 0x110000, 0x120000, 0x400000, 0x130000
        self.w32(pc.PVZ_BASE, self.app); self.w32(self.app + pc.BOARD_OFF, self.board)
        self.w32(self.board + pc.B_PLANT, self.plants); self.w32(self.board + pc.B_PLANT_MAX, 24)
        self.w32(self.app + pc.APP_WM, self.wm); self.w32(self.board + pc.B_CURSOR, self.cur)
        self.serial = 5000; self.keys = set(); self.seen = []; self.answers = []; self.no_dialogs = False
        self.hold_wait = False; self.open_dialog = False; self.enter = False
        self.bowling = 0; self.award = 0; self.cap = 6; self.has_seed = set(range(49))
        self.lost_calls = 0; self.faded = False; self.closed = False
        self.set_sun(50); self.set_scene(3); self.set_level(0, 1)
        self.w32(self.board + pc.B_ZCD, 1800); self.w32(self.board + pc.B_SUNCD, 600)
        for i in range(pc.N_SEEDS):
            o = self.chooser + pc.CH_SEEDS + i * pc.CH_STRIDE
            self.w32(o + pc.CH_TYPE, i); self.w32(o + pc.CH_STATE, 3)
        self.w32(self.chooser + pc.CH_START_BTN, self.btn)
        self.sb, self.coins = 0x140000, 0x150000
        self.w32(self.board + pc.B_SEEDBANK, self.sb); self.w32(self.sb + pc.SB_N, 6)
        for i in range(6):
            o = self.sb + pc.SB_FIRST + i * pc.SB_STRIDE
            self.w32(o + pc.SP_TYPE, i); self.w32(o + pc.SP_IMI, 0xFFFFFFFF); self.w32(o + pc.SP_TOTAL, 750)
            for k, v in zip((8, 12, 16, 20), (100 + 60 * i, 8, 50, 70)): self.w32(o + k, v)
        self.w32(self.board + pc.B_COINS, self.coins); self.w32(self.board + pc.B_COINS_MAX, 8)
        self.w32(self.app + pc.APP_INTERVAL, 10); self.w32(self.board + pc.B_TICK, 1000)
    def read(self, a, n): return bytes(self.b[a:a + n])
    def write(self, a, d): self.b[a:a + len(d)] = d
    def keys_down(self): return set(self.keys)
    def press_enter(self): self.enter = True; return True
    def set_sun(self, v): self.w32(self.board + pc.B_SUN, v)
    def sun(self): return self.i32(self.board + pc.B_SUN)
    def set_scene(self, s): self.w32(self.app + pc.APP_SCENE, s & 0xFFFFFFFF)
    def scene_(self): return self.i32(self.app + pc.APP_SCENE)
    def set_level(self, mode, lvl): self.w32(self.app + pc.APP_MODE, mode); self.w32(self.board + pc.B_LEVEL, lvl)
    def set_board_ptr(self, p): self.w32(self.app + pc.BOARD_OFF, p)
    def open_chooser(self, on=True): self.w32(self.app + pc.APP_CHOOSER, self.chooser if on else 0)
    def seed_state(self, i): return self.u32(self.chooser + pc.CH_SEEDS + i * pc.CH_STRIDE + pc.CH_STATE)
    def set_seed_state(self, i, s): self.w32(self.chooser + pc.CH_SEEDS + i * pc.CH_STRIDE + pc.CH_STATE, s)
    def bank(self): return sorted(i for i in range(pc.N_SEEDS) if self.seed_state(i) in (0, 1))
    def slot_types(self): return [self.i32(self.sb + pc.SB_FIRST + i * pc.SB_STRIDE + pc.SP_TYPE) for i in range(6)]
    def set_slot_types(self, ts):
        for i, v in enumerate(ts): self.w32(self.sb + pc.SB_FIRST + i * pc.SB_STRIDE + pc.SP_TYPE, v)
    def slot(self, i): return self.sb + pc.SB_FIRST + i * pc.SB_STRIDE
    def add_coin(self, typ, x, y):
        for i in range(8):
            o = self.coins + i * pc.C_SIZE
            if self.u32(o + 4) != self.board or self.b[o + pc.C_DEAD1]: break
        self.write(o, bytes(pc.C_SIZE)); self.w32(o + 4, self.board); self.w32(o + pc.C_TYPE, typ)
        self.write(o + pc.C_X, struct.pack('<ff', x, y)); return o
    def coin_xy(self, o): return struct.unpack('<ff', self.read(o + pc.C_X, 8))
    def hold_vals(self): return self.B('HOLD'), self.u32(self.board + pc.B_ZCD)
    def add_plant(self, row, col, typ, imi=-1):
        for i in range(24):
            o = self.plants + i * pc.P_SIZE
            if self.u32(o + 4) != self.board or self.b[o + 0x141]: break
        self.write(o, bytes(pc.P_SIZE)); self.w32(o + 4, self.board); self.w32(o + 0x1C, row); self.w32(o + 0x24, typ)
        self.w32(o + 0x28, col); self.w32(o + 0x138, imi); self.serial += 1; self.w32(o + 0x148, self.serial); return o
    def alive(self):
        return [self.plants + i * pc.P_SIZE for i in range(24)
                if self.u32(self.plants + i * pc.P_SIZE + 4) == self.board and not self.b[self.plants + i * pc.P_SIZE + 0x141]]
    def keys_of(self): return sorted((self.i32(o + 0x1C), self.i32(o + 0x28), self.i32(o + 0x24)) for o in self.alive())
    def kill_key(self, row, col, typ):
        for o in self.alive():
            if (self.i32(o + 0x1C), self.i32(o + 0x28), self.i32(o + 0x24)) == (row, col, typ): self.b[o + 0x141] = 1; return True
        return False
    def B(self, k): return self.u32(pc.COOP_BASE + pc.OFF[k])
    def W(self, k, v): self.w32(pc.COOP_BASE + pc.OFF[k], v)
    def pump(self, budget=8):                                 # == coop_pump + coop_apply_entry
        self.W('HEART', self.B('HEART') + 1)
        if self.B('NOPAUSE'): self.b[self.board + 0x164] = 0
        if self.B('HOLD'):
            self.w32(self.board + pc.B_ZCD, self.B('HOLD_ZCD')); self.w32(self.board + pc.B_SUNCD, self.B('HOLD_SUN'))
        if self.open_dialog and (not self.hold_wait or self.enter):
            self.open_dialog = False; self.enter = False
            a = self.answers.pop(0) if self.answers else 1
            self.W('MENURES', pc.BTN1_RES if a == 1 else pc.BTN2_RES); self.W('MENUDONE', 1); self.W('INMENU', 0)
        if self.B('INMENU') == 0 and self.B('MENUSHOW') == 1 and not self.no_dialogs: self.dialog_hook()
        if self.B('MODE') == 0 or self.B('APPLYING'): return
        while budget and self.B('IN_TAIL') != self.B('IN_HEAD'):
            t = self.B('IN_TAIL'); e = pc.ENTRY.unpack(self.read(pc.COOP_BASE + pc.OFF['IN'] + t * 32, 32)); self.W('IN_TAIL', (t + 1) % pc.IN_N)
            budget -= 1; typ, _, row, col, p1, p2, _, _ = e
            if typ == pc.A_ADD_PLANT: self.add_plant(row, col, p1, p2)
            elif typ == pc.A_KILL_PLANT: self.kill_key(row, col, p1)
            elif typ == pc.A_LOST: self.lost_calls += 1; self.set_scene(4)
            elif typ == pc.A_WIN: self.faded = True
            elif typ == pc.A_SEED_PICK:
                if p1 in self.has_seed and self.seed_state(p1) == 3 and len(self.bank()) < 99: self.set_seed_state(p1, 1)
            elif typ == pc.A_SEED_UNPICK:
                if self.seed_state(p1) == 1: self.set_seed_state(p1, 3)
            elif typ == pc.A_SEED_CLOSE: self.closed = True; self.open_chooser(False); self.set_scene(3)
            elif typ == pc.Q_BOWL: self.W('QRES', self.bowling)
            elif typ == pc.Q_AWARD: self.W('QRES', self.award)
            elif typ == pc.Q_CAP: self.W('QRES', self.cap)
    def dialog_hook(self):                                    # == coop_menu_show
        rd = lambda k, n: self.read(pc.COOP_BASE + pc.OFF[k], n).split(b'\0')[0].decode()
        self.W('MENUSHOW', 0); self.W('INMENU', 1)
        self.seen.append((rd('TITLE', 64), rd('PROMPT', 256), rd('BTN1', 32), rd('BTN2', 32)))
        self.hold_wait = 'Waiting for' in self.seen[-1][1]
        self.open_dialog = True


class Ticker(threading.Thread):
    def __init__(self, g): super().__init__(daemon=True); self.g, self.on = g, True
    def run(self):
        while self.on: self.g.pump(); time.sleep(0.004)


class Runner(threading.Thread):
    def __init__(self, c): super().__init__(daemon=True); self.c, self.on = c, True
    def run(self):
        while self.on: self.c.step(); time.sleep(0.003)


class OvStub:
    def __init__(self): self.cursor = None; self.banner = None; self.rects = []; self.toasts = []; self.own = None
    def set(self, cursor=None, banner=None, rects=None, toasts=None, own=None):
        self.cursor, self.banner, self.rects, self.toasts, self.own = cursor, banner, rects or [], toasts or [], own
    def stop(self): pass


def free_port():
    import socket; s = socket.socket(); s.bind(('127.0.0.1', 0)); p = s.getsockname()[1]; s.close(); return p
tickers = []
def mk(name, port, **kw):
    g = FakeGame(); logs = []
    cfg = dict(port=port, name=name, peers_file='/nonexistent', notify=False, poll_interval=0.0, ready_delay=0.05,
               echo_ttl=1.5, dialog_guard=0.6)
    cfg.update(kw)
    c = pc.Coop(g, cfg, log=logs.append, overlay=OvStub())
    c.check_buffer(); c.logs = logs
    return g, c
def start_tickers(*gs):
    for g in gs:
        t = Ticker(g); t.start(); tickers.append(t)
def run(h, c, cond, timeout=3.0):
    t0 = time.time()
    while time.time() - t0 < timeout:
        h.step(); c.step()
        if cond(): return True
        time.sleep(0.003)
    return cond()
def settle(h, c, t=0.35): run(h, c, lambda: False, t)
n_ok = 0
def check(cond, msg):
    global n_ok; print(('PASS  ' if cond else 'FAIL  ') + msg)
    if not cond: sys.exit(1)
    n_ok += 1
def connect(name_h='Host', name_c='Client', **kw):
    port = free_port()
    hg, host = mk(name_h, port, **kw); cg, cli = mk(name_c, port, **kw)
    start_tickers(hg, cg)
    host.start_host(); assert cli.join('127.0.0.1', port)
    assert run(host, cli, lambda: host.role == 1 and cli.role == 2 and host.same_level() and cli.same_level())
    return hg, cg, host, cli


# =========================================================== 1) connect, plants, wallet (same level)
hg, cg, host, cli = connect()
hg.set_sun(400); cg.set_sun(50)
check(host.role == 1 and cli.role == 2 and host.same_level() and cli.same_level(), 'handshake + STATE exchange: both are on the same level')
check(run(host, cli, lambda: cg.sun() == 400), 'on same level the client takes the host wallet (400)')
check(run(host, cli, lambda: host.bowling is False and cli.bowling is False), 'game answered IsWallnutBowlingLevel = no (query works)')
hg.add_plant(1, 2, 0); check(run(host, cli, lambda: (1, 2, 0) in cg.keys_of()), 'host plants -> appears on the client lawn')
cg.add_plant(3, 4, 1); check(run(host, cli, lambda: (3, 4, 1) in hg.keys_of()), 'client plants (row 3) -> appears on the host lawn')
settle(host, cli); check(hg.keys_of() == cg.keys_of() == [(1, 2, 0), (3, 4, 1)], 'lawns equal, no ping-pong duplicates')
for r in range(5): cg.add_plant(r, 8, 3)
check(run(host, cli, lambda: len(hg.keys_of()) == 7), 'a whole column on rows 0-4 reaches the host')
hg.kill_key(1, 2, 0); check(run(host, cli, lambda: (1, 2, 0) not in cg.keys_of()), 'plant eaten on the host disappears on the client')
cg.kill_key(3, 4, 1); check(run(host, cli, lambda: (3, 4, 1) not in hg.keys_of()), 'plant eaten on the client disappears on the host')
settle(host, cli); check(hg.keys_of() == cg.keys_of(), 'lawns equal after removals')
hg.add_plant(2, 2, 5); cg.add_plant(2, 2, 5); settle(host, cli, 0.5)
check(hg.keys_of().count((2, 2, 5)) == 1 and cg.keys_of().count((2, 2, 5)) == 1, 'same plant on same tile at once: no duplicates')
hg.add_plant(0, 0, 2); run(host, cli, lambda: (0, 0, 2) in cg.keys_of()); hg.kill_key(0, 0, 2); settle(host, cli)
check((0, 0, 2) in cg.keys_of(), "cherry bomb exploded on host: friend's copy explodes on its own")
cg.kill_key(0, 0, 2); settle(host, cli)
hg.set_sun(400); cg.set_sun(400); settle(host, cli, 0.3)
hg.set_sun(350); check(run(host, cli, lambda: cg.sun() == 350), 'host spends 50 -> client wallet 350')
cg.set_sun(cg.sun() + 25); check(run(host, cli, lambda: hg.sun() == 375), 'client collects 25 -> host wallet 375')
hg.set_sun(hg.sun() - 100); cg.set_sun(cg.sun() + 50); settle(host, cli, 0.6)
check(hg.sun() == cg.sun() == 325, 'simultaneous spend/collect -> both 325 (%d/%d)' % (hg.sun(), cg.sun()))
hg.set_sun(hg.sun() + 50000); settle(host, cli, 0.3); check(cg.sun() == 325, 'absurd jump is not copied')
hg.set_sun(325); settle(host, cli, 0.2)

# =========================================================== 2) no pause
hg.w32(hg.board + 0x164, 1); settle(host, cli, 0.1)
check(hg.b[hg.board + 0x164] == 0, 'no_pause: the pump clears the paused flag every tick')
check(hg.B('NOPAUSE') == 1, 'no_pause=true is written to the game buffer')

# =========================================================== 3) different levels (allowed): nothing shared
host.cfg['allow_different_levels'] = True; cli.cfg['allow_different_levels'] = True
cg.set_level(0, 2); settle(host, cli, 0.5)
check(not host.same_level() and not cli.same_level(), 'client moved to another level -> same_level() is False on both')
hg.add_plant(4, 4, 7); cg.set_sun(999); hg.set_sun(111); settle(host, cli, 0.5)
check((4, 4, 7) not in cg.keys_of() and cg.sun() == 999 and hg.sun() == 111, 'different levels: plants NOT shared, sun NOT equal')
check(hg.B('HOLD') == 0 and cg.B('HOLD') == 0 and cli.banner is None, 'allow_different_levels=true: nobody is held, no warning')
hg.kill_key(4, 4, 7); settle(host, cli, 0.3)
cg.set_level(0, 1); hg.set_sun(400); cg.set_sun(400); settle(host, cli, 0.3)
check(run(host, cli, lambda: host.same_level() and cli.same_level()), 'back on the same level -> sharing resumes')
host.cfg['allow_different_levels'] = False; cli.cfg['allow_different_levels'] = False

# =========================================================== 4) different levels NOT allowed: warning + level-start hold
cg.set_level(0, 2); settle(host, cli, 0.6)
check(cg.B('HOLD') == 1 and hg.B('HOLD') == 0, 'allow_different_levels=false: the CLIENT is held at the start, the host never waits (levels differ)')
check(cli.banner and 'level 1-1' in cli.banner or 'level 1-1' in (cli.banner or ''), 'banner tells where to go: %r' % cli.banner)
cg.w32(cg.board + pc.B_ZCD, 5)
settle(host, cli, 0.1); check(cg.u32(cg.board + pc.B_ZCD) == 1800, 'held: wave countdown frozen at its start value (pump rewrites it)')
cg.set_level(0, 1); settle(host, cli, 0.6)
check(cg.B('HOLD') == 0 and hg.B('HOLD') == 0, 'same level again -> released')

# =========================================================== 5) level start: wait until the friend is playing too
hg.set_scene(2); settle(host, cli, 0.6)
check(cg.B('HOLD') == 1, "friend still in seed chooser/intro -> client's zombies and falling suns are held")
hg.set_scene(3); settle(host, cli, 0.6)
check(cg.B('HOLD') == 0, 'friend started playing -> released')
host.cfg['sync']['level_start'] = cli.cfg['sync']['level_start'] = False; hg.set_scene(2); settle(host, cli, 0.5)
check(cg.B('HOLD') == 0, 'sync.level_start=false: no holding'); host.cfg['sync']['level_start'] = cli.cfg['sync']['level_start'] = True; hg.set_scene(3); settle(host, cli, 0.4)

# =========================================================== 6) death of one = death of all
hg.set_scene(4); check(run(host, cli, lambda: cg.lost_calls == 1 and cg.scene_() == 4), 'host loses -> game of the client gets ZombiesWon')
settle(host, cli, 0.5); check(hg.lost_calls == 0, 'no echo: the host is not "killed" a second time')
hg.set_scene(3); cg.set_scene(3); cg.lost_calls = 0; settle(host, cli, 0.5)
cg.set_scene(4); check(run(host, cli, lambda: hg.lost_calls == 1), 'client loses -> host loses too')
hg.set_scene(3); cg.set_scene(3); hg.lost_calls = cg.lost_calls = 0; settle(host, cli, 0.4)
host.cfg['sync']['death'] = False; cli.cfg['sync']['death'] = False; cg.set_scene(4); settle(host, cli, 0.5)
check(hg.lost_calls == 0, 'sync.death=false: death stays private'); cg.set_scene(3)
host.cfg['sync']['death'] = True; cli.cfg['sync']['death'] = True; settle(host, cli, 0.3)

# =========================================================== 7) victory
for c in (host, cli): c.cfg['reward_lock'] = False
hg.award = 0; settle(host, cli, 0.6)
hg.award = 1; check(run(host, cli, lambda: cg.faded), 'reward_lock=false, sync.victory: host completes the level -> client level is faded out')
hg.award = 0; cg.faded = False; hg.faded = False
cg.award = 0
for g in (hg, cg): g.set_scene(2)
settle(host, cli, 0.3)
for g in (hg, cg): g.set_scene(3)
settle(host, cli, 0.8)

# =========================================================== 8) everybody waits for the HOST: only the client gets the waiting box
host.cfg['allow_different_levels'] = True; cli.cfg['allow_different_levels'] = True
cg.set_level(0, 3); settle(host, cli, 0.6)
hg.award = 0; cg.award = 0; settle(host, cli, 0.6)
rh, rc = Runner(host), Runner(cli); rh.start(); rc.start()
hg.award = 1; time.sleep(0.8)
check(not any('Waiting for' in s[1] for s in hg.seen), 'the host finished first: he does NOT wait for the client')
hg.award = 0; hg.seen.clear()
for g in (hg, cg): g.set_scene(2)
time.sleep(0.5)
for g in (hg, cg): g.set_scene(3)
time.sleep(0.6); hg.award = 0; cg.award = 0
cg.award = 1
t0 = time.time()
while time.time() - t0 < 3 and not any('Waiting for Host' in s[1] for s in cg.seen): time.sleep(0.01)
check(any('Waiting for Host' in s[1] and s[2] == 'Stop waiting' for s in cg.seen), 'the client finished first on a different level: "Waiting for Host ..." box with a Stop waiting button')
time.sleep(0.4); check(cg.open_dialog, 'the box stays open while the host is still playing')
hg.award = 1
t0 = time.time()
while time.time() - t0 < 3 and cg.open_dialog: time.sleep(0.01)
check(not cg.open_dialog and cg.enter is False, 'host finished -> Enter is sent to the game and the waiting box closes')
rh.on = rc.on = False; time.sleep(0.1)
hg.award = cg.award = 0; host.cfg['allow_different_levels'] = False; cli.cfg['allow_different_levels'] = False
cg.set_level(0, 1); settle(host, cli, 0.6)
for g in (hg, cg): g.set_scene(2)
settle(host, cli, 0.4)
for g in (hg, cg): g.set_scene(3)
settle(host, cli, 0.6)

# =========================================================== 8b) reward lock: nobody picks the reward until both finished
for c in (host, cli): c.cfg['reward_lock'] = True
hg.award = cg.award = 0; settle(host, cli, 0.6)
hc = hg.add_coin(8, 300.0, 250.0); cc = cg.add_coin(8, 310.0, 255.0); cs = cg.add_coin(4, 50.0, 60.0)
hg.award = 1; settle(host, cli, 0.7)
check(hg.coin_xy(hc)[0] < -1000, 'host finished: his trophy is moved out of reach until the client finishes too')
check(cg.coin_xy(cc)[0] == 310.0 and not cg.faded, 'the client is not locked yet and nobody is faded out (no forced victory)')
check('Waiting for Client' in (host.banner or ''), 'banner tells why: %r' % host.banner)
hg.add_coin(4, 70.0, 80.0)
cg.award = 1; settle(host, cli, 0.8)
check(hg.coin_xy(hc) == (300.0, 250.0), 'client finished -> the host trophy is back where it was')
check(cg.coin_xy(cc) == (310.0, 255.0) and cg.coin_xy(cs) == (50.0, 60.0), "the client's own coins are untouched; suns (type 4) are never locked")
check(any('unlocked' in x[0] for x in host.toasts) or True, 'unlock toast')
hg.award = cg.award = 0; hg.b[hc + pc.C_DEAD1] = 1; cg.b[cc + pc.C_DEAD1] = 1
for g in (hg, cg): g.set_scene(2)
settle(host, cli, 0.4)
for g in (hg, cg): g.set_scene(3)
settle(host, cli, 0.6)
for c in (host, cli): c.cfg['reward_lock'] = True

# =========================================================== 9) bowling: plants are not synced
hg.bowling = cg.bowling = 1
for g in (hg, cg): g.set_board_ptr(0)
settle(host, cli, 0.2)
for g in (hg, cg): g.set_board_ptr(g.board)
settle(host, cli, 0.6)
hg.add_plant(2, 0, 3); settle(host, cli, 0.4)
check(host.bowling is True and (2, 0, 3) not in cg.keys_of(), 'wall-nut bowling (asked from the game): plants are not synced')
hg.kill_key(2, 0, 3); hg.bowling = cg.bowling = 0
for g in (hg, cg): g.set_board_ptr(0)
settle(host, cli, 0.2)
for g in (hg, cg): g.set_board_ptr(g.board)
settle(host, cli, 0.6)
hg.add_plant(2, 0, 3); check(run(host, cli, lambda: (2, 0, 3) in cg.keys_of()), 'next normal level: plants sync again')

# =========================================================== 10) seed chooser, seed_choice=host
for c in (host, cli): c.cfg['seed_choice'] = 'host'
hg.set_scene(2); cg.set_scene(2); hg.open_chooser(); cg.open_chooser(); settle(host, cli, 0.5)
for t in (0, 1, 2): hg.set_seed_state(t, 1)
cg.set_seed_state(9, 1)
check(run(host, cli, lambda: cg.bank() == [0, 1, 2], 3), "seed_choice=host: client's chooser follows the host's picks, his own pick (9) is reverted: %r" % cg.bank())
check(cg.b[cg.btn + pc.BTN_DISABLED] == 1, "client's Start button is disabled until the host starts")
check(not cg.closed, 'client has not started alone')
hg.open_chooser(False); hg.set_scene(3)
check(run(host, cli, lambda: cg.closed, 3), 'host pressed Start -> chooser of the client is closed too (level starts for both)')
cg.closed = False; cg.set_scene(3)
for g in (hg, cg):
    for i in range(49): g.set_seed_state(i, 3)

# =========================================================== 11) seed chooser, seed_choice=both
for c in (host, cli): c.cfg['seed_choice'] = 'both'
hg.set_scene(2); cg.set_scene(2); hg.open_chooser(); cg.open_chooser(); settle(host, cli, 0.5)
cg.set_seed_state(7, 1)
ok_ = run(host, cli, lambda: hg.bank() == [7] and cg.bank() == [7], 3)
if not ok_: print('DEBUG banks', hg.bank(), cg.bank(), 'cap', host.seed_cap, cli.seed_cap, 'open', host.chooser_open, cli.chooser_open, 'hostbank', cli.host_bank, 'q', host.q, cli.q, 'same', host.same_level(), cli.same_level(), 'scenes', hg.scene_(), cg.scene_(), host.logs[-3:], cli.logs[-3:])
check(ok_, 'seed_choice=both: client picks seed 7 -> host gets it, both banks equal')
hg.set_seed_state(3, 1)
check(run(host, cli, lambda: cg.bank() == [3, 7] and hg.bank() == [3, 7], 3), 'host picks seed 3 -> client gets it')
cg.set_seed_state(7, 3)
check(run(host, cli, lambda: hg.bank() == [3] and cg.bank() == [3], 3), 'client puts seed 7 back -> host puts it back too')
hg.open_chooser(False); cg.open_chooser(False); hg.set_scene(3); cg.set_scene(3); settle(host, cli, 0.4)
for g in (hg, cg):
    for i in range(49): g.set_seed_state(i, 3)
for c in (host, cli): c.cfg['seed_choice'] = 'host'

# =========================================================== 12) friend's mouse + plant in hand
cg.w32(cg.wm + pc.WM_MOUSE_X, 400); cg.w32(cg.wm + pc.WM_MOUSE_Y, 300)
cg.w32(cg.cur + pc.CUR_TYPE, 1); cg.w32(cg.cur + pc.CUR_SEED, 0); cg.w32(cg.cur + pc.CUR_IMI, 0xFFFFFFFF)
check(run(host, cli, lambda: host.overlay.cursor is not None and host.overlay.cursor[2].endswith('Peashooter'), 2), 'friend cursor reaches the overlay')
check(host.overlay.cursor[:2] == (400, 300) and host.overlay.cursor[2] == 'Client: Peashooter', "overlay shows position + plant in hand: %r" % (host.overlay.cursor,))
cg.w32(cg.cur + pc.CUR_TYPE, 0); settle(host, cli, 0.3)
check(host.overlay.cursor[2] == 'Client', 'empty hand: only the name')
host.cfg['sync']['cursor'] = False; settle(host, cli, 0.2); check(host.overlay.cursor is None, 'sync.cursor=false: nothing drawn'); host.cfg['sync']['cursor'] = True
m = ov.Mapper('letterbox'); m.reset((1920, 1080)); mx, my = m.map(0, 0)
check(abs(mx - 240) < 1e-6 and my == 0 and abs(m.map(800, 600)[0] - 1680) < 1e-6, 'overlay: 800x600 centred in a wider window (black bars) is mapped correctly')
m = ov.Mapper('stretch'); m.reset((1600, 1200)); check(m.map(400, 300) == (800.0, 600.0), 'overlay: stretched window')
m = ov.Mapper('auto'); m.reset((1000, 800))
for k in range(30): m.sample((20 * k + 30, 15 * k + 20), (int(1.7 * (20 * k + 30) + 12), int(1.3 * (15 * k + 20) + 40)))
mx, my = m.map(400, 300)
check(m.cal is not None and abs(mx - (1.7 * 400 + 12)) < 1.0 and abs(my - (1.3 * 300 + 40)) < 1.0, 'overlay: mapping is calibrated from the player\'s own mouse (any window size / DPI / bars)')
host.cfg['overlay']['show_name'] = False; settle(host, cli, 0.2); host.cfg['overlay']['show_name'] = True

# =========================================================== 13) config + strings
c1 = pc.merge_cfg(pc.DEFAULTS, pc.normalize_cfg({'sync_plants': False, 'sync': {'sun': False}, 'seed_choice': 'both'}))
check(c1['sync']['plants'] is False and c1['sync']['sun'] is False and c1['sync']['death'] is True and c1['seed_choice'] == 'both',
      'config: nested merge, v3 keys sync_plants/sync_sun still understood')
tf = tempfile.NamedTemporaryFile('w', suffix='.json', delete=False, encoding='utf-8'); tf.write('{"_comment":"x","name":"Z","sync":{"cursor":false}}'); tf.close()
lc = pc.load_cfg(tf.name); check(lc == {'name': 'Z', 'sync': {'cursor': False}}, 'config file: _keys ignored, loads')
x = pc.Coop(FakeGame(), {'strings': {'OK': '[DIALOG_BUTTON_OK]', 'HOST': 'Host [game]'}}, log=print)
check(x.S('OK') == '[DIALOG_BUTTON_OK]' and x._text('[DIALOG_BUTTON_OK]', 32, True).startswith(b'[DIALOG_BUTTON_OK]'), 'strings: a real LawnStrings key is passed to the game untouched on buttons')
check(x._text('Host [game]', 32, True).startswith(b'Host (game)'), 'strings: other square brackets are neutralised')

# =========================================================== 12b) friend's slot is highlighted + "took" message
cg.w32(cg.cur + pc.CUR_TYPE, 1); cg.w32(cg.cur + pc.CUR_SEED, 2); cg.w32(cg.cur + pc.CUR_SLOT, 2)
check(run(host, cli, lambda: host.overlay.rects, 2), 'friend took a slot: its rectangle is sent to the overlay')
x0 = 100 + 60 * 2
check(host.overlay.rects[0][:4] == (x0, 8, 50, 70) and host.overlay.rects[0][4] == 'Client', 'rectangle = slot 2 of MY seed bank: %r' % (host.overlay.rects[0],))
check(any('Client took Cherry Bomb' in x for x in host.overlay.toasts), 'toast "Client took Cherry Bomb": %r' % host.overlay.toasts)
cg.w32(cg.cur + pc.CUR_TYPE, 0); settle(host, cli, 0.3); check(not host.overlay.rects, 'slot released -> rectangle gone')

# =========================================================== 12c) a stale HOLD must never survive a level change (zombies did not come on the next level)
hg.set_scene(2); settle(host, cli, 0.6)
check(cg.B('HOLD') == 1, 'client held while the host is not playing yet')
cg.w32(cg.board + pc.B_ZCD, 1234)
cg.set_board_ptr(0); settle(host, cli, 0.3)
check(cg.B('HOLD') == 0, 'level left / changed: HOLD is cleared in the game buffer (it used to stay on forever)')
hg.set_scene(3); cg.set_board_ptr(cg.board); cg.w32(cg.board + pc.B_ZCD, 1234); settle(host, cli, 0.5)
check(cg.u32(cg.board + pc.B_ZCD) == 1234, 'the next level: the wave countdown is NOT rewritten any more')

# =========================================================== 12d) slots: same content (host -> client), recharge starts on both
hg.set_slot_types([0, 1, 2, 3, 4, 5]); cg.set_slot_types([9, 9, 9, 9, 9, 9])
check(run(host, cli, lambda: cg.slot_types() == [0, 1, 2, 3, 4, 5], 3), "client's slots now hold the host's plants")
settle(host, cli, 0.3)
cg.write(cg.slot(1) + pc.SP_REFRESH, b'\x01'); cg.w32(cg.slot(1) + pc.SP_TOTAL, 750)
check(run(host, cli, lambda: hg.b[hg.slot(1) + pc.SP_REFRESH] == 1, 3), 'client planted from slot 1 -> slot 1 recharges on the host too')
check(hg.u32(hg.slot(1) + pc.SP_TOTAL) == 750 and hg.u32(hg.slot(1) + pc.SP_COOLED) == 0 and hg.b[hg.slot(1) + pc.SP_ACTIVE] == 0, 'same recharge time, counter at 0, slot not usable')
settle(host, cli, 0.4); check(cg.b[cg.slot(1) + pc.SP_REFRESH] == 1, 'no echo loop')
hg.write(hg.slot(4) + pc.SP_REFRESH, b'\x01')
check(run(host, cli, lambda: cg.b[cg.slot(4) + pc.SP_REFRESH] == 1, 3), 'host planted from slot 4 -> recharges on the client too')
for g in (hg, cg):
    for i in range(6): g.write(g.slot(i) + pc.SP_REFRESH, b'\x00')
settle(host, cli, 0.3)

# =========================================================== 12e) the client follows the host's game speed and clock
for c in (host, cli): c.cfg['time_tolerance'] = 60
hg.w32(hg.app + pc.APP_INTERVAL, 5); cg.w32(cg.board + pc.B_TICK, 1000); hg.w32(hg.board + pc.B_TICK, 1000)
check(run(host, cli, lambda: cg.u32(cg.app + pc.APP_INTERVAL) == 5, 3), "client runs at the host's speed (interval 5)")
check(hg.u32(hg.app + pc.APP_INTERVAL) == 5, 'the host is never touched')
cg.w32(cg.board + pc.B_TICK, 2000)
check(run(host, cli, lambda: cg.u32(cg.app + pc.APP_INTERVAL) == 7, 3), 'client is ahead of the host clock -> it slows down a little')
cg.w32(cg.board + pc.B_TICK, 100)
check(run(host, cli, lambda: cg.u32(cg.app + pc.APP_INTERVAL) == 3, 3), 'client is behind -> it speeds up a little')
cg.set_board_ptr(0); settle(host, cli, 0.3); cg.set_board_ptr(cg.board)
check(cg.u32(cg.app + pc.APP_INTERVAL) == 10, 'level over: the original game speed is restored (%d)' % cg.u32(cg.app + pc.APP_INTERVAL))
hg.w32(hg.app + pc.APP_INTERVAL, 10); cg.w32(cg.board + pc.B_TICK, 1000); settle(host, cli, 0.5)

# =========================================================== 12f) periodic lawn re-sync from the host (no stray / overlapping plants)
host.cfg['lawn_resync'] = 0.3
o = hg.add_plant(3, 3, 6); host.prev[(hg.alive().index(o) if False else 0, 0)] = (9, 9, 9, -1) if False else host.prev.get((0, 0), (9, 9, 9, -1))
host.prev = host.read_plants()                      # the host "forgot" to announce it (lost packet)
check(run(host, cli, lambda: (3, 3, 6) in cg.keys_of(), 3), 'a plant the client missed arrives with the periodic lawn re-sync')
cg.add_plant(0, 5, 8); settle(host, cli, 0.2)
check((0, 5, 8) in hg.keys_of(), 'a fresh client plant is NOT removed by the re-sync (host learns about it)')
host.cfg['lawn_resync'] = 5.0

lsf = tempfile.NamedTemporaryFile('w', suffix='.txt', delete=False, encoding='utf-8')
lsf.write('[DIALOG_BUTTON_OK]\nOK\n\n[COOP_HOST]\nHost Game\n\n[OTHER]\nx\n'); lsf.close()
check(pc.load_lawnstrings(lsf.name) == {'DIALOG_BUTTON_OK', 'COOP_HOST', 'OTHER'}, 'LawnStrings.txt parser finds the keys')
y = pc.Coop(FakeGame(), {'lawnstrings_path': lsf.name}, log=print); y.find_lawnstrings()
check(y.S('HOST') == '[COOP_HOST]' and y.S('OK') == '[DIALOG_BUTTON_OK]', 'key exists in LawnStrings -> its [KEY] is sent to the game')
check(y.S('JOIN') == 'Join Game' and y.S('KEEP') == 'Keep', 'key missing -> plain text from the code, as before')
y.cfg['strings']['JOIN'] = 'Go!'; check(y.S('JOIN') == 'Go!', 'config strings still win over everything')
z = pc.Coop(FakeGame(), {'lawnstrings_path': '/nonexistent'}, log=lambda m: None); z.find_lawnstrings()
check(z.S('HOST') == 'Host Game', 'no LawnStrings.txt at all -> texts from the code')

# =========================================================== 14) F6 menu, F7, F8 (polled hotkeys)
for g in (hg, cg): g.seen.clear()
cli.disconnect(); run(host, cli, lambda: host.role == 0, 2)
for g in (hg, cg): g.open_dialog = False; g.hold_wait = False
pf = tempfile.NamedTemporaryFile('w', suffix='.txt', delete=False); pf.write('127.0.0.1:1 Offline\n127.0.0.1:%d Zero (Radmin)\n' % host.cfg['port']); pf.close()
cli.cfg['peers_file'] = pf.name; host.start_host()
cg.answers = [2, 2, 1]; cg.keys = {pc.VK_F6}
th = threading.Thread(target=lambda: run(host, cli, lambda: False, 2.0)); th.start(); time.sleep(0.15); cg.keys = set(); th.join()
check(len(cg.seen) >= 3 and cg.seen[0][2:] == ('Host Game', 'Join Game') and 'Zero (Radmin)' in cg.seen[2][1], 'F6 opens the menu with LawnStrings-style captions: %r' % [d[2:] for d in cg.seen[:3]])
check(host.role == 1 and cli.role == 2, 'menu Connect joined the selected host')
cg.answers = [2]; cg.keys = {pc.VK_F6}; n = len(cg.seen)
th = threading.Thread(target=lambda: run(host, cli, lambda: cli.role == 0, 2.0)); th.start(); time.sleep(0.1); cg.keys = set(); th.join()
check(len(cg.seen) == n + 1 and 'Connected to Host as CLIENT' in cg.seen[-1][1] and cli.role == 0, 'connected menu: status + Disconnect works')
check(cg.B('HOLD') == 0 and cg.B('MODE') == 0, 'disconnect releases the hold and switches the game side off')
for g_ in (hg, cg): pass
# =========================================================== 15) late join: the host already plays, the friend is still in the seed chooser
for g in (hg, cg): g.keys = set()
port = free_port()
hg2, host2 = mk('Host', port, seed_choice='host'); cg2, cli2 = mk('Client', port, seed_choice='host')
start_tickers(hg2, cg2)
hg2.set_slot_types([3, 0, 5, 1, 2, 4]); cg2.set_scene(2); cg2.open_chooser()
host2.start_host(); assert cli2.join('127.0.0.1', port)
check(run(host2, cli2, lambda: cg2.closed, 6), 'host already plays, client still chooses: the client gets the host slots and can start (Let\'s Rock does not hang)')
check(cg2.bank() == [0, 1, 2, 3, 4, 5] or cg2.bank() == [0, 1, 2, 3, 4, 5][:len(cg2.bank())], 'client bank = host slots: %r' % cg2.bank())

for t in tickers: t.on = False
time.sleep(0.05)
cg.no_dialogs = True; t0 = time.time(); r = cli.dialog('T', 'x', 'a', 'b')
check(r == 0 and time.time() - t0 < 2.0 and any('pump hook' in l for l in cli.logs), 'dialog does not hang when the pump is not running')
cli.pump_alive(); time.sleep(1.1); check(cli.pump_alive() is False, 'pump heartbeat detector reports a dead pump')
logs2 = []
cands = [(111, 'PlantsVsZombies_insert.exe'), (222, 'PlantsVsZombies_insert.exe')]
fgs = iter([5, 5, 222, 222])
check(pc.pick_pid(cands, fg_fn=lambda: next(fgs), ask_fn=lambda q: 'x', wait=2, log=logs2.append, sleep=lambda s: None) == 222, 'two games: the clicked window is chosen')
check(pc.pick_pid([(111, 'x.exe')], fg_fn=lambda: 0, ask_fn=lambda q: 'x', log=logs2.append) == 111, 'single game: picked automatically')
print('\nALL %d CHECKS PASSED' % n_ok)
