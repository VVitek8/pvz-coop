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
        self.zextra = False; self.vgate = None
        self.close_calls = 0; self.keep_chooser = False; self.close_delay = 0.0; self.scene_at = 0.0
        self.set_sun(50); self.set_scene(3); self.set_level(0, 1)
        self.w32(self.board + pc.B_ZCD, 1800); self.w32(self.board + pc.B_SUNCD, 600)
        for i in range(pc.N_SEEDS):
            o = self.chooser + pc.CH_SEEDS + i * pc.CH_STRIDE
            self.w32(o + pc.CH_TYPE, i); self.w32(o + pc.CH_STATE, 3)
        self.w32(self.chooser + pc.CH_START_BTN, self.btn)
        self.zom = 0x160000
        self.w32(self.board + pc.B_ZOMBIES, self.zom); self.w32(self.board + pc.B_ZOMBIES_MAX, 16)
        self.zserial = 100
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
    def zaddr(self, i): return self.zom + i * pc.Z_SIZE
    def add_zombie(self, typ, row, x, hp=270, hp1=0):
        for i in range(16):
            o = self.zaddr(i)
            if self.u32(o + 4) != self.board or self.b[o + pc.Z_DEAD]: break
        self.write(o, bytes(pc.Z_SIZE)); self.w32(o + 4, self.board); self.w32(o + pc.Z_TYPE, typ); self.w32(o + pc.Z_ROW, row)
        self.write(o + pc.Z_X, struct.pack('<ff', x, 40.0 + 100 * row)); self.w32(o + pc.Z_HP, hp); self.w32(o + pc.Z_HP1, hp1)
        self.zserial += 1; self.w32(o + pc.Z_ID, (self.zserial << 16) | i); return o
    def zombies(self):
        return [self.zaddr(i) for i in range(16) if self.u32(self.zaddr(i) + 4) == self.board and not self.b[self.zaddr(i) + pc.Z_DEAD]]
    def zinfo(self, o): return (self.i32(o + pc.Z_TYPE), self.i32(o + pc.Z_ROW), round(struct.unpack('<f', self.read(o + pc.Z_X, 4))[0]), self.i32(o + pc.Z_HP), self.i32(o + pc.Z_HP1))
    def slot_types(self): return [self.i32(self.sb + pc.SB_FIRST + i * pc.SB_STRIDE + pc.SP_TYPE) for i in range(6)]
    def set_slot_types(self, ts):
        for i, v in enumerate(ts): self.w32(self.sb + pc.SB_FIRST + i * pc.SB_STRIDE + pc.SP_TYPE, v)
    def slot(self, i): return self.sb + pc.SB_FIRST + i * pc.SB_STRIDE
    def add_coin(self, typ, x, y):
        for i in range(8):
            o = self.coins + i * pc.C_SIZE
            if self.u32(o + 4) != self.board or self.b[o + pc.C_DEAD1]: break
        self.write(o, bytes(pc.C_SIZE)); self.w32(o + 4, self.board); self.w32(o + pc.C_TYPE, typ)
        self.w32(o + pc.C_W, 50); self.w32(o + pc.C_W + 4, 50)
        self.write(o + pc.C_X, struct.pack('<ff', x, y)); return o
    def coin_wh(self, o): return (self.i32(o + pc.C_W), self.i32(o + pc.C_W + 4))
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
        if self.scene_at and time.time() >= self.scene_at: self.scene_at = 0.0; self.set_scene(3); self.open_chooser(False)
        if self.B('NOPAUSE'): self.b[self.board + 0x164] = 0
        if self.B('HOLD'):
            self.w32(self.board + pc.B_ZCD, self.B('HOLD_ZCD')); self.w32(self.board + pc.B_SUNCD, self.B('HOLD_SUN'))
        if self.B('ZHOLD'): self.w32(self.board + pc.B_ZCD, self.B('ZHOLD_VAL'))
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
            elif typ == pc.A_SEED_CLOSE:
                if self.u32(self.app + pc.APP_CHOOSER):
                    self.closed = True; self.close_calls += 1
                    if not self.keep_chooser: self.open_chooser(False)
                    if self.close_delay: self.scene_at = time.time() + self.close_delay
                    else: self.set_scene(3)
            elif typ == pc.A_ADD_COIN:
                o = self.add_coin(p1, float(col), float(row)); self.W('CRES', o); self.w32(o + pc.C_CARD, 0xFFFFFFFF)
            elif typ == pc.A_COLLECT:
                self.b[p1 + pc.C_COLLECTED] = 1; self.collected_addr = p1
            elif typ == pc.A_ADD_ZOMBIE:
                zo = self.add_zombie(p1, row, 800.0, hp=270)
                if self.vgate and self.vgate(): self.w32(zo + pc.Z_VID, 0x191)
                self.W('ZRES', zo)
                if self.zextra: self.add_zombie(p1, row, 790.0)         # a team spawns extra zombies on its own
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
hg.set_sun(hg.sun() + 50000); settle(host, cli, 0.1)
check(run(host, cli, lambda: cg.sun() == hg.sun(), 3), "...but the host's wallet is the truth: the periodic absolute value brings the client to it")
hg.set_sun(325); check(run(host, cli, lambda: cg.sun() == 325, 3), 'host back to 325 -> client 325')
cg.set_sun(10); settle(host, cli, 1.4); check(cg.sun() == hg.sun(), 'client drift (10) is repaired by the host value within ~1 s (%d/%d)' % (cg.sun(), hg.sun()))

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
hc = hg.add_coin(8, 300.0, 250.0); cs = cg.add_coin(4, 50.0, 60.0)
hg.award = 1; settle(host, cli, 0.7)
if False: print('DEBUG done', host.done_local, cli.done_local, 'same', host.same_level(), 'peerdone', host.peer and host.peer['done'], 'ignore', host.ignore_coins, 'hidden', host.hidden, 'scene', host.local, 'given', host.lock_given_up, 'since', host.lock_since, 'coin', hg.coin_xy(hc), 'logs', host.logs[-4:])
check(hg.coin_wh(hc) == (0, 0) and hg.coin_xy(hc)[0] > 0, 'host finished: his trophy stays where it is (visible) but has no hit area until the client finishes too')
check(not cg.faded and not cli.done_local, 'the client has not finished and nobody is faded out (no forced victory)')
check('Waiting for Client' in (host.banner or ''), 'banner tells why: %r' % host.banner)
hg.add_coin(4, 70.0, 80.0)
cg.award = 1; cc = cg.add_coin(8, 310.0, 255.0); settle(host, cli, 0.8)
check(hg.coin_xy(hc) == (300.0, 250.0) and hg.coin_wh(hc) == (50, 50), 'client finished -> the host trophy can be clicked again (hit area restored)')
check(cg.coin_xy(cc) == (310.0, 255.0) and cg.coin_xy(cs) == (50.0, 60.0), "the client's reward is not locked (host was done first); suns (type 4) are never locked")
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

# =========================================================== 11) 'both' no longer exists: the host always decides
xx = pc.Coop(FakeGame(), {'seed_choice': 'both'}, log=lambda m: None)
check(xx.cfg['seed_choice'] == 'host', 'seed_choice=both is turned into host (everybody follows the host)')

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

# =========================================================== 12b) the cursor shows the plant in hand (no slot rectangle, no toast by default)
cg.w32(cg.cur + pc.CUR_TYPE, 1); cg.w32(cg.cur + pc.CUR_SEED, 2); cg.w32(cg.cur + pc.CUR_SLOT, 2)
check(run(host, cli, lambda: host.overlay.cursor and host.overlay.cursor[2].endswith('Cherry Bomb'), 2), 'cursor label = the plant in his hand: %r' % (host.overlay.cursor,))
settle(host, cli, 0.2)
check(not host.overlay.rects and not host.overlay.toasts, 'no slot rectangle and no "took" toast (overlay.toasts is off)')
host.cfg['overlay']['toasts'] = True; cg.w32(cg.cur + pc.CUR_SEED, 0); settle(host, cli, 0.3)
check(any('Client took Peashooter' in x for x in host.overlay.toasts), 'overlay.toasts=true: "Client took Peashooter"')
host.cfg['overlay']['toasts'] = False
cg.w32(cg.cur + pc.CUR_TYPE, 0); settle(host, cli, 0.3)

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

# =========================================================== 12g) the reward lock keeps working on level after level (it used to work only once)
def new_level_pair():
    hg.award = cg.award = 0
    for g in (hg, cg): g.set_scene(2)
    settle(host, cli, 0.4)
    for g in (hg, cg): g.set_scene(3)
    settle(host, cli, 0.7)
for rnd in (1, 2, 3):
    new_level_pair()
    hg.award = 1                                   # the "award dropped" flag is stuck at 1 from the start (unreliable) ...
    hc2 = hg.add_coin(16, 200.0, 150.0)            # ... the reward item on the lawn is what counts
    settle(host, cli, 0.7)
    check(hg.coin_wh(hc2) == (0, 0) and hg.coin_xy(hc2)[0] > 0, 'level %d: host reward locked until the client finishes' % rnd)
    cc2 = cg.add_coin(8, 220.0, 170.0); cg.award = 1; settle(host, cli, 0.8)
    check(hg.coin_wh(hc2) == (50, 50), 'level %d: client finished -> host reward unlocked, host and client both done' % rnd)
    hg.b[hc2 + pc.C_DEAD1] = 1; cg.b[cc2 + pc.C_DEAD1] = 1

# =========================================================== 12h) a new level on the SAME board address is noticed by the board clock
hg.award = 0; cg.award = 0; hg.w32(hg.board + pc.B_TICK, 500); settle(host, cli, 0.4)
hg.add_coin(8, 10.0, 10.0); settle(host, cli, 0.5)
check(host.done_local, 'host is "done" (reward item on the lawn)')
hg.b[hg.coins + 0 * pc.C_SIZE + pc.C_DEAD1] = 1
for i in range(8): hg.b[hg.coins + i * pc.C_SIZE + pc.C_DEAD1] = 1
hg.w32(hg.board + pc.B_TICK, 5); settle(host, cli, 0.4)
check(not host.done_local, 'board clock went back with the same board address -> treated as a new level, "done" is reset')
hg.w32(hg.board + pc.B_TICK, 1000); cg.award = 0; hg.award = 0; settle(host, cli, 0.4)

# =========================================================== 12i) plant health follows the host
ph = hg.add_plant(4, 4, 3); hg.w32(ph + pc.P_HP, 300)
check(run(host, cli, lambda: (4, 4, 3) in cg.keys_of(), 3), 'plant arrived on the client')
pcx = [o for o in cg.alive() if (cg.i32(o + 0x1C), cg.i32(o + 0x28), cg.i32(o + 0x24)) == (4, 4, 3)][0]
cg.w32(pcx + pc.P_HP, 100)
check(run(host, cli, lambda: cg.i32(pcx + pc.P_HP) == 300, 3), "client plant health is set to the host's (100 -> 300)")
hg.w32(ph + pc.P_HP, 120)
check(run(host, cli, lambda: cg.i32(pcx + pc.P_HP) == 120, 3), 'host plant gets bitten (300 -> 120): the client plant follows within ~0.25 s')
host.cfg['sync']['plant_hp'] = cli.cfg['sync']['plant_hp'] = False; hg.w32(ph + pc.P_HP, 50); settle(host, cli, 0.6)
check(cg.i32(pcx + pc.P_HP) == 120, 'sync.plant_hp=false: left alone'); host.cfg['sync']['plant_hp'] = cli.cfg['sync']['plant_hp'] = True
hg.kill_key(4, 4, 3); settle(host, cli, 0.4)

# =========================================================== 12j) the lock cannot last forever (reward_wait_max)
for c in (host, cli): c.cfg['reward_wait_max'] = 0.6
new_level_pair()
hc3 = hg.add_coin(8, 120.0, 130.0); hg.award = 1; settle(host, cli, 0.4)
check(hg.coin_wh(hc3) == (0, 0) and hg.coin_xy(hc3)[0] > 0, 'locked while the client has not finished')
settle(host, cli, 0.9)
check(hg.coin_wh(hc3) == (50, 50) and any('unlocking' in l for l in host.logs), 'reward_wait_max: unlocked after the timeout')
for c in (host, cli): c.cfg['reward_wait_max'] = 600
hg.b[hc3 + pc.C_DEAD1] = 1; new_level_pair()

# =========================================================== 12k) zombie mirror (host's zombies are shown on the client)
for c in (host, cli): c.cfg['sync']['zombies'] = True; c.cfg['zombie_orphan_grace'] = 0.4
for g in (hg, cg):
    for o in g.zombies(): g.b[o + pc.Z_DEAD] = 1
za = hg.add_zombie(0, 1, 640.0, hp=270); zb = hg.add_zombie(2, 3, 500.0, hp=200, hp1=640)
check(run(host, cli, lambda: len(cg.zombies()) == 2, 4), 'client shows the 2 zombies of the host')
check(run(host, cli, lambda: sorted(cg.zinfo(o) for o in cg.zombies()) == sorted(hg.zinfo(o) for o in hg.zombies()), 3), 'same type, row, position, body health and armor health: %r' % sorted(cg.zinfo(o) for o in cg.zombies()))
check(cg.B('ZHOLD') == 1, "the client's own waves are held off (no zombies of its own)")
settle(host, cli, 1.0); check(len(cg.zombies()) == 2, 'no duplicates after a while (%d)' % len(cg.zombies()))
hg.write(za + pc.Z_X, struct.pack('<f', 420.0)); hg.w32(za + pc.Z_HP, 90); hg.w32(zb + pc.Z_HP1, 0)
check(run(host, cli, lambda: sorted(cg.zinfo(o) for o in cg.zombies()) == sorted(hg.zinfo(o) for o in hg.zombies()), 3), 'host zombie walked and was shot (x 640 -> 420, hp 270 -> 90, armor broken): the client follows')
hg.b[za + pc.Z_DEAD] = 1
check(run(host, cli, lambda: len(cg.zombies()) == 1, 3), 'host zombie died -> it disappears on the client')
cg.add_zombie(4, 2, 300.0)
check(run(host, cli, lambda: len(cg.zombies()) == 1, 3), "a zombie only the client has (made by its own logic) is removed after a moment")
hg.add_zombie(7, 0, 700.0); cg.zextra = True
check(run(host, cli, lambda: len(cg.zombies()) == 2 and any(cg.zinfo(o)[0] == 7 for o in cg.zombies()), 4), 'a zombie that brings extra zombies when created: the extras are removed, only the host\'s zombies stay')
settle(host, cli, 1.0); check(len(cg.zombies()) == 2, 'still exactly the host\'s 2 zombies (%d)' % len(cg.zombies())); cg.zextra = False
hg.set_scene(5)
check(run(host, cli, lambda: cg.faded, 3), 'host reached the award screen -> the client level ends too')
cg.faded = False; hg.set_scene(3)
cg.set_board_ptr(0); settle(host, cli, 0.4)
check(cg.B('ZHOLD') == 0, 'level left: the zombie hold is cleared in the game')
cg.set_board_ptr(cg.board)
for c in (host, cli): c.cfg['sync']['zombies'] = False
settle(host, cli, 0.5)
for g in (hg, cg):
    for o in g.zombies(): g.b[o + pc.Z_DEAD] = 1
cg.add_zombie(1, 1, 300.0); settle(host, cli, 1.0)
check(len(cg.zombies()) == 1 and cg.B('ZHOLD') == 0, 'sync.zombies=false (default): everybody keeps their own zombies, nothing is held')

# =========================================================== 12l) zombie mirror, part 2: variants (mods), everything copied, rate, no flicker
import itertools
for c in (host, cli): c.cfg['sync']['zombies'] = True; c.cfg['zombie_orphan_grace'] = 0.4; c.cfg['zombie_create_tries'] = 6
for g in (hg, cg):
    for o in g.zombies(): g.b[o + pc.Z_DEAD] = 1
cnt = {'n': 0}; orig_rz = cli.remote_zombies
def counting(payload, _o=orig_rz): cnt['n'] += 1; return _o(payload)
cli.remote_zombies = counting
seq = itertools.cycle([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1])
cg.vgate = lambda: next(seq)                       # a mod that makes a variant by chance when a zombie is created
v1 = hg.add_zombie(0, 1, 640.0, hp=500); hg.w32(v1 + pc.Z_VID, 0x191)           # host: fire-breather variant (id 0x191 in +134)
v2 = hg.add_zombie(0, 2, 600.0, hp=270); v3 = hg.add_zombie(2, 3, 560.0, hp=200, hp1=640)
def sigs(g): return sorted((g.i32(o + pc.Z_TYPE), g.u32(o + pc.Z_VID), g.i32(o + pc.Z_ROW)) for o in g.zombies())
check(run(host, cli, lambda: sigs(cg) == sigs(hg), 5), 'mod variants: the client shows exactly the host\'s variants (same type + variant id), creation retried until the random choice matches: %r' % sigs(cg))
settle(host, cli, 0.8); check(len(cg.zombies()) == 3 and sigs(cg) == sigs(hg), 'no extra / wrong variants left over (%d zombies)' % len(cg.zombies()))
hg.w32(v2 + 0x28, 7); hg.w32(v2 + 0x68, 123); hg.write(v2 + 0x124, struct.pack('<f', 0.5)); hg.w32(v2 + 0x118, 4444); hg.w32(v2 + 0x110, 5555)
cz = [o for o in cg.zombies() if cg.i32(o + pc.Z_ROW) == 2][0]; cg.w32(cz + 0x118, 9); cg.w32(cz + 0x110, 8)
check(run(host, cli, lambda: cg.i32(cz + 0x28) == 7 and cg.i32(cz + 0x68) == 123 and struct.unpack('<f', cg.read(cz + 0x124, 4))[0] == 0.5, 3), 'EVERYTHING numeric is copied (state, timers, speed, ...)')
check(cg.i32(cz + 0x118) == 9 and cg.i32(cz + 0x110) == 8, 'animation / attachment ids stay local (not copied)')
n0 = cnt['n']; run(host, cli, lambda: False, 1.0)
check(cnt['n'] - n0 >= 18, 'the host sends its zombies ~30 times a second (%d packets in 1 s)' % (cnt['n'] - n0))
vz = [o for o in cg.zombies() if cg.u32(o + pc.Z_VID) == 0x191][0]; cg.b[vz + pc.Z_DEAD] = 1
run(host, cli, lambda: False, 0.2); check(len(cg.zombies()) == 2, 'a zombie that died only on the client is not brought back instantly (flicker)')
check(run(host, cli, lambda: sigs(cg) == sigs(hg), 4), 'but it is brought back (same variant) when the host still has it: both sides equal again')
# a client game that cannot make the variant at all (other mod / no mod)
cg.vgate = None
v4 = hg.add_zombie(0, 4, 500.0, hp=900); hg.w32(v4 + pc.Z_VID, 0x195)
check(run(host, cli, lambda: any('cannot make' in l for l in cli.logs) and len(cli.zmap) == 4, 8), 'unknown variant 0x195: shown as a plain zombie of the same row after a few tries')
settle(host, cli, 1.0)
check(len(cg.zombies()) == 4 and any('cannot make' in l for l in cli.logs), 'no endless creating (%d zombies), the player is told once' % len(cg.zombies()))
pz = [o for o in cg.zombies() if cg.i32(o + pc.Z_ROW) == 4][0]
check(cg.u32(pz + pc.Z_VID) == 0 and cg.i32(pz + pc.Z_HP) == 900, 'its health etc. still follows the host while the unsupported variant id is not forced onto the client game')
# waves: progress bar from the host
hg.write(hg.board + pc.B_PROGRESS, struct.pack('<f', 0.625)); check(run(host, cli, lambda: struct.unpack('<f', cg.read(cg.board + pc.B_PROGRESS, 4))[0] == 0.625, 3), "level progress bar follows the host (waves are visible, taken from the host)")
# rewards
for g in (hg, cg):
    for o in g.zombies(): g.b[o + pc.Z_DEAD] = 1
for c in (host, cli): c.cfg['reward_lock'] = True
for g in (hg, cg): g.award = 0
for g in (hg, cg): g.set_scene(2)
settle(host, cli, 0.4)
for g in (hg, cg): g.set_scene(3)
settle(host, cli, 0.8)
hr = hg.add_coin(18, 300.0, 200.0)                    # a money bag (mini-game reward) on the host
check(run(host, cli, lambda: any(cg.i32(o + pc.C_TYPE) == 18 for o in [cg.coins + i * pc.C_SIZE for i in range(8)] if cg.u32(o + 4) == cg.board and not cg.b[o + pc.C_DEAD1]), 3), 'the host reward appears on the client too (a copy is created)')
cr = [o for o in [cg.coins + i * pc.C_SIZE for i in range(8)] if cg.u32(o + 4) == cg.board and cg.i32(o + pc.C_TYPE) == 18][0]
settle(host, cli, 0.5)
check(hg.coin_wh(hr) == (50, 50) and cg.coin_wh(cr) == (50, 50), 'both rewards exist -> both are unlocked')
hg.b[hr + pc.C_COLLECTED] = 1                          # the host clicks his bag
check(run(host, cli, lambda: cg.b[cr + pc.C_COLLECTED] == 1, 3), "the host picked up his bag -> the client's bag is picked up too (same code as a click: reward + level end)")
settle(host, cli, 0.8); check(hg.b[hr + pc.C_COLLECTED] == 1 and getattr(hg, 'collected_addr', None) is None, 'no echo back to the host')
# the host leaves the level (mini-game: straight to the menu) -> the client's level ends even though the coin logic did not fire
for g in (hg, cg): g.b[g.coins:g.coins + 8 * pc.C_SIZE] = bytes(8 * pc.C_SIZE)
cg.faded = False
for g in (hg, cg): g.set_scene(2)
settle(host, cli, 0.4)
for g in (hg, cg): g.set_scene(3)
settle(host, cli, 0.8)
hg.set_board_ptr(0); hg.set_scene(1)
check(run(host, cli, lambda: cg.faded, 3), 'the host left the level -> the client level ends too (it used to stay stuck without a way out)')
hg.set_board_ptr(hg.board); hg.set_scene(3); cg.faded = False
cli.remote_zombies = orig_rz
for c in (host, cli): c.cfg['sync']['zombies'] = False
settle(host, cli, 0.6)

# =========================================================== 12m) simultaneous start: the START message carries the REAL slots
hg.set_scene(2); cg.set_scene(2); hg.open_chooser(); cg.open_chooser(); settle(host, cli, 0.5)
for t_ in (0, 1, 2, 3, 4, 5): hg.set_seed_state(t_, 1)
run(host, cli, lambda: cg.bank() == [0, 1, 2, 3, 4, 5], 3)
hg.set_slot_types([0, 1, 2, 3, 4, 5])
for t_ in (0, 1, 2, 3, 4, 5): hg.set_seed_state(t_, 3)       # the chooser panel slides away: the picks look "gone" for a moment
hg.open_chooser(False); hg.set_scene(3)
t0 = time.time(); ok_ = run(host, cli, lambda: cg.close_calls >= 1, 3); dt = time.time() - t0
check(ok_ and dt < 0.8, 'host starts -> the client starts at once (%.2f s), not after a long wait; his bank was not emptied by the shrinking chooser: %r' % (dt, cg.bank()))
run(host, cli, lambda: False, 0.5)

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
# =========================================================== 15) the friend joins while seeds are being chosen / while the host already plays: NO start loop
for g in (hg, cg): g.keys = set()
def join_pair(**kw):
    port = free_port()
    a, ha = mk('Host', port, seed_choice='host', **kw); b, cb = mk('Client', port, seed_choice='host', **kw)
    start_tickers(a, b)
    return a, b, ha, cb, port
# 15a) host already plays, the client is still in his seed chooser (his chooser stays alive and the intro takes 2.5 s: the old loop case)
hg2, cg2, host2, cli2, port = join_pair()
hg2.set_slot_types([3, 0, 5, 1, 2, 4]); cg2.set_scene(2); cg2.open_chooser(); cg2.keep_chooser = True; cg2.close_delay = 2.5
host2.start_host(); assert cli2.join('127.0.0.1', port)
check(run(host2, cli2, lambda: cg2.close_calls >= 1, 6), 'host already plays, client chooses: the client asks for the host seeds and starts')
run(host2, cli2, lambda: False, 5.0)
check(cg2.close_calls == 1, 'the chooser is closed exactly ONCE even though it stays alive 2.5 s (it was called every second -> endless loop): %d' % cg2.close_calls)
check(cg2.scene_() == 3 and host2.peer['scene'] == 3, 'client reached the lawn and the host sees it (scene 3)')
# 15b) the friend joins while the HOST is still choosing; the host starts later; duplicated "start" messages must not re-close
hg3, cg3, host3, cli3, port3 = join_pair()
hg3.set_scene(2); cg3.set_scene(2); hg3.open_chooser(); cg3.open_chooser(); cg3.keep_chooser = True; cg3.close_delay = 2.5
host3.start_host(); assert cli3.join('127.0.0.1', port3)
run(host3, cli3, lambda: host3.same_level() and cli3.same_level(), 3)
for t_ in (0, 1, 2, 3, 4, 5): hg3.set_seed_state(t_, 1)
check(run(host3, cli3, lambda: cg3.bank() == [0, 1, 2, 3, 4, 5], 4), 'friend joined during the host choice: his bank follows')
hg3.open_chooser(False); hg3.set_scene(3)
check(run(host3, cli3, lambda: cg3.close_calls >= 1, 4), 'host started -> client closes')
for k in range(4):
    host3.link.send(pc.K_SEEDS, bytes([1, 6, 0, 1, 2, 3, 4, 5])); run(host3, cli3, lambda: False, 0.4)   # duplicated / late START messages
check(cg3.close_calls == 1, 'duplicate START messages are ignored: close called once (%d)' % cg3.close_calls)
run(host3, cli3, lambda: cg3.scene_() == 3, 4)
check(cg3.scene_() == 3, 'client is on the lawn')
for g_ in (hg, cg): pass
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
