"""Generate candidate rooms for one curriculum slot.

usage: python3 tools/generate_rooms.py SLOT SEED COUNT ENTER_SIDE EXIT_SIDE  >  tools/candidates/slot.jsonl

Each room is a randomly generated corridor maze (depth-first search, a few loops knocked through, a few
open plazas) with an entrance arch, an exit door, hearts in dead ends, emerald blocks, water placed on the
route to the door (so a bridge is forced) and, from slot 3 on, patrolling and hunting enemies in the plazas.
Every candidate is solved by the C++ breadth-first solver (tools/solve.cpp), so each line printed is a room
that is solvable, together with its exact optimum.  Rooms whose enemies do not actually matter are dropped.
tools/build_levels.py then picks the curriculum from these candidates."""
import random, subprocess, sys, json, os
from rules import parse, run, won

HERE = os.path.dirname(os.path.abspath(__file__))
SOLVE = os.path.join(HERE, 'solve')

# slot -> (width, height, hearts, blocks, water on the route, extra water, patrols, hunters,
#          probability of knocking out each interior wall (loops), open plazas)
# Sizes are odd so the maze lines up.  Later rooms are bigger and busier.
PARAMS = [
    (11, 9, 2, 0, 0, 0, 0, 0, .10, 0), (11, 9, 2, 2, 0, 0, 0, 0, .10, 1), (13, 9, 2, 2, 1, 0, 0, 0, .08, 1),
    (13, 11, 3, 3, 1, 0, 1, 0, .08, 1), (15, 11, 3, 3, 1, 1, 1, 0, .08, 2), (15, 11, 3, 4, 2, 0, 2, 0, .06, 2),
    (17, 11, 4, 3, 2, 0, 1, 1, .06, 2), (17, 13, 4, 3, 2, 1, 1, 1, .06, 2), (19, 13, 4, 3, 2, 1, 1, 1, .05, 3),
    (19, 13, 5, 3, 3, 0, 1, 1, .05, 3), (19, 13, 5, 3, 3, 0, 1, 1, .05, 3), (21, 13, 5, 3, 3, 1, 1, 1, .04, 3),
]
SIDES = {'U': (-1, 0), 'D': (1, 0), 'L': (0, -1), 'R': (0, 1)}   # (d row, d col)
OPPS = {'U': 'D', 'D': 'U', 'L': 'R', 'R': 'L'}

def bfs_path(g, src, dst):
    from collections import deque
    h, w = len(g), len(g[0]); prev = {src: None}; q = deque([src])
    while q:
        p = q.popleft()
        if p == dst: break
        for dr, dc in SIDES.values():
            n = (p[0] + dr, p[1] + dc)
            if 0 <= n[0] < h and 0 <= n[1] < w and g[n[0]][n[1]] != '#' and n not in prev:
                prev[n] = p; q.append(n)
    if dst not in prev: return None
    out = []; p = dst
    while p is not None: out.append(p); p = prev[p]
    return out[::-1]

def room(rng, slot, enter, leave):
    w, h, nh, nb, nwr, nwx, npat, nhunt, braid, nplaza = PARAMS[slot]
    g = [['#'] * w for _ in range(h)]
    # randomized DFS maze on odd cells
    stack = [(1, 1)]; g[1][1] = '.'
    while stack:
        r, c = stack[-1]; opts = []
        for dr, dc in SIDES.values():
            nr, nc = r + 2 * dr, c + 2 * dc
            if 1 <= nr < h - 1 and 1 <= nc < w - 1 and g[nr][nc] == '#': opts.append((dr, dc))
        if not opts: stack.pop(); continue
        dr, dc = rng.choice(opts); g[r + dr][c + dc] = '.'; g[r + 2 * dr][c + 2 * dc] = '.'; stack.append((r + 2 * dr, c + 2 * dc))
    for r in range(1, h - 1):               # braid: knock out some walls to make loops
        for c in range(1, w - 1):
            if g[r][c] == '#' and (r % 2) != (c % 2) and rng.random() < braid: g[r][c] = '.'
    for _ in range(nplaza):                 # open turning plazas
        pr_, pc_ = rng.randrange(1, h - 3, 2), rng.randrange(1, w - 3, 2)
        for r in range(pr_, pr_ + 3):
            for c in range(pc_, pc_ + 3): g[r][c] = '.'
    def door(side):
        if side in 'UD': c = rng.randrange(1, w - 1, 2); r = 0 if side == 'U' else h - 1
        else: r = rng.randrange(1, h - 1, 2); c = 0 if side == 'L' else w - 1
        return r, c
    er, ec = door(enter); xr, xc = door(leave)
    while (xr, xc) == (er, ec): xr, xc = door(leave)
    g[er][ec] = 'N'; g[xr][xc] = 'E'
    pr, pc = er + SIDES[OPPS[enter]][0], ec + SIDES[OPPS[enter]][1]; g[pr][pc] = 'P'
    xin = (xr + SIDES[OPPS[leave]][0], xc + SIDES[OPPS[leave]][1]); g[xin[0]][xin[1]] = '.'
    route = bfs_path(g, (pr, pc), xin)
    if route is None or len(route) < 8: return None
    used = {(pr, pc), xin}
    inner = route[2:-2]; rng.shuffle(inner)
    water = []
    for q in inner:
        if len(water) >= nwr: break
        if all(abs(q[0] - o[0]) + abs(q[1] - o[1]) > 2 for o in water) and g[q[0]][q[1]] == '.': water.append(q)
    if len(water) < nwr: return None
    for q in water: g[q[0]][q[1]] = '~'; used.add(q)
    free = [(r, c) for r in range(1, h - 1) for c in range(1, w - 1) if g[r][c] == '.' and (r, c) not in used]
    rng.shuffle(free)
    def nbrs(q): return sum(1 for dr, dc in SIDES.values() if g[q[0] + dr][q[1] + dc] != '#')
    dead = [q for q in free if nbrs(q) == 1]; other = [q for q in free if nbrs(q) != 1]
    def take(pool, n):
        out = []
        while pool and len(out) < n: out.append(pool.pop())
        return out
    hearts = take(dead, nh); hearts += take(other, nh - len(hearts))
    if len(hearts) < nh: return None
    for q in hearts: g[q[0]][q[1]] = 'H'
    rest = [q for q in free if g[q[0]][q[1]] == '.']; rng.shuffle(rest)
    for q in take(rest, nb): g[q[0]][q[1]] = 'B'
    for q in take(rest, nwx): g[q[0]][q[1]] = '~'
    def openness(q): return sum(1 for dr, dc in SIDES.values() if g[q[0] + dr][q[1] + dc] not in '#N')
    far = [q for q in rest if abs(q[0] - pr) + abs(q[1] - pc) > 4]
    far.sort(key=lambda q: (openness(q) < 3, rng.random()))      # enemies live in plazas / junctions, where they can be dodged
    far = far[::-1]                                              # take() pops from the end
    for q in take(far, npat): g[q[0]][q[1]] = rng.choice('^v<>')
    for q in take(far, nhunt): g[q[0]][q[1]] = rng.choice('udlr')
    return [''.join(r) for r in g]

def solve(rows, cap):
    """Run the C++ solver.  Returns (optimal move string, states explored), or (None, None) if the room is
    unsolvable or needs more than `cap` states."""
    p = subprocess.run([SOLVE, str(cap)], input='\n'.join(rows) + '\n', capture_output=True, text=True)
    t = p.stdout.split()
    if t and t[0] == 'OPT': return t[3], int(t[2])
    return None, None

def strip_enemies(rows):
    """The same room with its enemies removed."""
    return [''.join('.' if ch in '^v<>udlr' else ch for ch in r) for r in rows]

def pushes(L, moves):
    """How many of the moves push a block."""
    from rules import step
    s = L['start']; n = 0
    for m in moves:
        t = step(L, s, m)
        if t[1] != s[1] or t[3] != s[3]: n += 1
        s = t
    return n

if __name__ == '__main__':
    slot, seed, count = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    enter, leave = sys.argv[4], sys.argv[5]
    rng = random.Random(seed * 1000 + slot)
    for _ in range(count):
        rows = room(rng, slot, enter, leave)
        if rows is None: continue
        sol, n = solve(rows, 500000)
        if sol is None: continue
        L = parse(rows)
        enemies = PARAMS[slot][6] + PARAMS[slot][7] > 0
        if enemies:
            s0, _ = solve(strip_enemies(rows), 500000)
            if s0 is None or won(L, run(L, s0)): continue      # enemies must matter
        print(json.dumps(dict(slot=slot, rows=rows, sol=sol, opt=len(sol), states=n, pushes=pushes(L, sol))), flush=True)
