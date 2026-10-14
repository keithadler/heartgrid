// Mirrors HeartGrid/Rules.lean and tools/rules.py exactly. Positions are [row, col]; sets use "r,c" keys.
(function () {
  const D = { U: [-1, 0], D: [1, 0], L: [0, -1], R: [0, 1] };
  const OPP = { U: 'D', D: 'U', L: 'R', R: 'L' };
  const PATROL = { '^': 'U', v: 'D', '<': 'L', '>': 'R' }, HUNT = { u: 'U', d: 'D', l: 'L', r: 'R' };
  const SIGHT = 6;
  const k = (r, c) => r + ',' + c;

  function parse(rows) {
    const L = { h: rows.length, w: rows[0].length, walls: new Set(), arch: null, exit: null };
    const s = { player: null, blocks: new Set(), hearts: new Set(), water: new Set(), enemies: [], dead: false };
    rows.forEach((row, r) => [...row].forEach((ch, c) => {
      const key = k(r, c);
      if (ch === '#') L.walls.add(key);
      else if (ch === 'N') { L.walls.add(key); L.arch = [r, c]; }
      else if (ch === 'B') s.blocks.add(key);
      else if (ch === 'H') s.hearts.add(key);
      else if (ch === '~') s.water.add(key);
      else if (ch === 'P') s.player = [r, c];
      else if (ch === 'E') L.exit = [r, c];
      else if (PATROL[ch]) s.enemies.push({ r, c, d: PATROL[ch], hunter: false });
      else if (HUNT[ch]) s.enemies.push({ r, c, d: HUNT[ch], hunter: true });
    }));
    return { L, start: s };
  }
  const clone = s => ({ player: s.player.slice(), blocks: new Set(s.blocks), hearts: new Set(s.hearts), water: new Set(s.water),
    enemies: s.enemies.map(e => ({ ...e })), dead: s.dead });
  const inB = (L, p) => p[0] >= 0 && p[0] < L.h && p[1] >= 0 && p[1] < L.w;
  const isExit = (L, p) => p[0] === L.exit[0] && p[1] === L.exit[1];

  // Direction in which an enemy at (r,c) sees the player, or null.
  function sees(L, s, r, c) {
    const [pr, pc] = s.player;
    if (r === pr && c === pc) return null;
    let d, dist;
    if (r === pr) { d = pc > c ? 'R' : 'L'; dist = Math.abs(pc - c); }
    else if (c === pc) { d = pr > r ? 'D' : 'U'; dist = Math.abs(pr - r); }
    else return null;
    if (dist > SIGHT) return null;
    const [dr, dc] = D[d];
    for (let i = 1; i < dist; i++) {
      const q = [r + dr * i, c + dc * i];
      if (L.walls.has(k(q[0], q[1])) || s.blocks.has(k(q[0], q[1])) || isExit(L, q)) return null;
    }
    return d;
  }

  function worldTurn(L, s) {
    const n = clone(s);
    for (let i = 0; i < n.enemies.length; i++) {
      const e = n.enemies[i];
      const free = q => inB(L, q) && !L.walls.has(k(q[0], q[1])) && !n.water.has(k(q[0], q[1])) && !n.blocks.has(k(q[0], q[1]))
        && !isExit(L, q) && !n.enemies.some((o, j) => j !== i && o.r === q[0] && o.c === q[1]);
      const sd = e.hunter ? sees(L, n, e.r, e.c) : null;
      if (sd) {
        e.d = sd; const q = [e.r + D[sd][0], e.c + D[sd][1]];
        if (free(q)) { e.r = q[0]; e.c = q[1]; }
      } else {
        const q = [e.r + D[e.d][0], e.c + D[e.d][1]];
        if (free(q)) { e.r = q[0]; e.c = q[1]; } else e.d = OPP[e.d];
      }
      if (e.r === n.player[0] && e.c === n.player[1]) { n.dead = true; return n; }
    }
    return n;
  }

  // a is 'U','D','L','R' or 'S' (wait).  Returns { state, moved, ... }; state === s when nothing happens.
  function step(L, s, a) {
    const none = { state: s, moved: false };
    if (s.dead || isExit(L, s.player)) return none;
    if (a === 'S') return { state: worldTurn(L, s), moved: true, waited: true };
    const [dr, dc] = D[a];
    const t = [s.player[0] + dr, s.player[1] + dc], tk = k(t[0], t[1]);
    if (!inB(L, t) || L.walls.has(tk) || s.water.has(tk)) return none;
    const n = clone(s);
    if (isExit(L, t)) {
      if (s.hearts.size) return { state: s, moved: false, locked: true };
      n.player = t; return { state: n, moved: true, event: 'win' };
    }
    const info = { moved: true };
    if (s.blocks.has(tk)) {
      const u = [t[0] + dr, t[1] + dc], uk = k(u[0], u[1]);
      if (!inB(L, u) || L.walls.has(uk) || isExit(L, u) || s.blocks.has(uk) || s.hearts.has(uk) || s.enemies.some(e => e.r === u[0] && e.c === u[1])) return none;
      n.blocks.delete(tk); n.player = t; info.pushed = true;
      if (s.water.has(uk)) { n.water.delete(uk); info.event = 'splash'; info.at = u; } else n.blocks.add(uk);
    } else {
      n.player = t;
      if (n.hearts.delete(tk)) { info.event = n.hearts.size ? 'heart' : 'open'; info.at = t; }
      if (s.enemies.some(e => e.r === t[0] && e.c === t[1])) { n.dead = true; info.event = 'dead'; return { ...info, state: n }; }
    }
    const w = worldTurn(L, n);
    if (w.dead) info.event = 'dead';
    return { ...info, state: w };
  }
  window.Engine = { parse, step, clone, sees };
})();
