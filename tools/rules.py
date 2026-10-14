"""Reference implementation of the HeartGrid rules (mirrors HeartGrid/Rules.lean, tools/solve.cpp, web/engine.js).

Map legend:
  # wall   N entrance arch (acts as wall)   . floor   ~ water   H heart   B emerald block
  P player start   E exit door (opens once no hearts remain)
  Patrol enemies  ^ v < >   (walk their facing direction, turn round when blocked)
  Hunters         u d l r   (patrol, but chase along row/column when they see you within SIGHT cells)
Actions: U D L R move, S wait.  A move that does nothing (blocked) is not a turn: enemies stay put.
State = (player, blocks, hearts, water, enemies, dead).  enemies = tuple of (r, c, dir, hunter).
"""
DIRS = {'U': (-1, 0), 'D': (1, 0), 'L': (0, -1), 'R': (0, 1)}
OPP = {'U': 'D', 'D': 'U', 'L': 'R', 'R': 'L'}
SIGHT = 6
PATROL = {'^': 'U', 'v': 'D', '<': 'L', '>': 'R'}
HUNT = {'u': 'U', 'd': 'D', 'l': 'L', 'r': 'R'}

def parse(rows):
    walls, blocks, hearts, water, enemies = set(), [], [], [], []
    p = e = None
    for r, row in enumerate(rows):
        for c, ch in enumerate(row):
            if ch in '#N': walls.add((r, c))
            elif ch == 'B': blocks.append((r, c))
            elif ch == 'H': hearts.append((r, c))
            elif ch == '~': water.append((r, c))
            elif ch == 'P': p = (r, c)
            elif ch == 'E': e = (r, c)
            elif ch in PATROL: enemies.append((r, c, PATROL[ch], False))
            elif ch in HUNT: enemies.append((r, c, HUNT[ch], True))
    return dict(h=len(rows), w=len(rows[0]), walls=frozenset(walls), exit=e,
                start=(p, tuple(sorted(blocks)), tuple(sorted(hearts)), tuple(sorted(water)), tuple(enemies), False))

def inb(L, q): return 0 <= q[0] < L['h'] and 0 <= q[1] < L['w']

def sees(L, s, e):
    """Direction in which hunter e sees the player (clear row/column within SIGHT), else None."""
    p, bl = s[0], s[1]
    r, c = e[0], e[1]
    if (r, c) == p: return None
    if r == p[0]:
        d = 'R' if p[1] > c else 'L'; dist = abs(p[1] - c)
    elif c == p[1]:
        d = 'D' if p[0] > r else 'U'; dist = abs(p[0] - r)
    else: return None
    if dist > SIGHT: return None
    dr, dc = DIRS[d]
    for i in range(1, dist):
        q = (r + dr * i, c + dc * i)
        if q in L['walls'] or q in bl or q == L['exit']: return None
    return d

def enemy_step(L, s, others, e):
    r, c, d, hunter = e
    def free(q):
        return (inb(L, q) and q not in L['walls'] and q not in s[3] and q not in s[1]
                and q != L['exit'] and q not in others)
    sd = sees(L, s, e) if hunter else None
    if sd is not None:
        dr, dc = DIRS[sd]; q = (r + dr, c + dc)
        return (q[0], q[1], sd, hunter) if free(q) else (r, c, sd, hunter)
    dr, dc = DIRS[d]; q = (r + dr, c + dc)
    return (q[0], q[1], d, hunter) if free(q) else (r, c, OPP[d], hunter)

def world_turn(L, s):
    p, bl, he, wa, en, dead = s
    done = []
    for i, e in enumerate(en):
        others = {(x[0], x[1]) for x in done} | {(x[0], x[1]) for x in en[i + 1:]}
        n = enemy_step(L, s, others, e)
        if (n[0], n[1]) == p:
            return (p, bl, he, wa, tuple(done) + (n,) + en[i + 1:], True)
        done.append(n)
    return (p, bl, he, wa, tuple(done), False)

def player_move(L, s, d):
    """New state after the player's own move (before enemies act), or None if the move is blocked."""
    p, bl, he, wa, en, dead = s
    dr, dc = DIRS[d]
    t = (p[0] + dr, p[1] + dc)
    if not inb(L, t) or t in L['walls'] or t in wa: return None
    epos = {(x[0], x[1]) for x in en}
    if t == L['exit']:
        return (t, bl, he, wa, en, False) if not he else None
    if t in bl:
        u = (t[0] + dr, t[1] + dc)
        if not inb(L, u) or u in L['walls'] or u == L['exit'] or u in bl or u in he or u in epos: return None
        nb = tuple(sorted(x for x in bl if x != t))
        if u in wa: return (t, nb, he, tuple(x for x in wa if x != u), en, False)
        return (t, tuple(sorted(nb + (u,))), he, wa, en, False)
    return (t, bl, tuple(x for x in he if x != t), wa, en, t in epos)

def step(L, s, a):
    if s[5] or s[0] == L['exit']: return s
    if a == 'S': return world_turn(L, s)
    n = player_move(L, s, a)
    if n is None: return s
    if n[0] == L['exit'] or n[5]: return n          # won, or walked into an enemy
    return world_turn(L, n)

def won(L, s): return s[0] == L['exit'] and not s[5]

def run(L, moves, s=None):
    s = L['start'] if s is None else s
    for m in moves: s = step(L, s, m)
    return s

def solve_py(L, limit=200000):
    from collections import deque
    s0 = L['start']; seen = {s0: None}; q = deque([s0])
    while q:
        s = q.popleft()
        if won(L, s):
            out = []
            while seen[s] is not None: s, d = seen[s]; out.append(d)
            return ''.join(reversed(out)), len(seen)
        for d in 'UDLRS':
            n = step(L, s, d)
            if n != s and n not in seen:
                seen[n] = (s, d); q.append(n)
                if len(seen) > limit: return None, len(seen)
    return None, len(seen)
