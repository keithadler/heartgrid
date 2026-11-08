/**
 * engine.js - the rules of HeartGrid, in plain JavaScript.
 *
 * This is a SEPARATE implementation of the rules that are written and proved in Lean 4 in
 * HeartGrid/Rules.lean (and mirrored in Python in tools/rules.py).  Nothing proves the copies are identical;
 * tests/test_cross_engine.py plays hundreds of random games through both and compares the outcomes.
 * So: if you change a rule here, change it in Rules.lean and tools/rules.py too, then run `make test`.
 *
 * Conventions used throughout this file:
 *   - A position is [row, col].  Row 0 is the TOP of the picture; the screen shows y = h - 1 - row.
 *   - Sets of cells store "r,c" strings (see k() below) because JavaScript Sets compare strings by value.
 *   - The engine never draws or reads the keyboard.  It only turns (room, state, action) into a new state.
 *
 * Room text (levels.js `rows`) uses one character per cell:
 *   #  wall          N  wall with the entrance arch (decoration only)     .  floor
 *   P  hero start    H  heart          B  emerald block      ~  water
 *   E  exit door     ^ v < >  patrolling ghost (letter = initial direction)
 *   u d l r          hunting ghost (letter = initial direction)
 */
(function () {
  // Row/column step for each direction letter.
  const D = { U: [-1, 0], D: [1, 0], L: [0, -1], R: [0, 1] };
  const OPP = { U: 'D', D: 'U', L: 'R', R: 'L' };               // used when a patrolling ghost turns round
  // Map room-text characters to the direction a ghost starts out facing.
  const PATROL = { '^': 'U', v: 'D', '<': 'L', '>': 'R' }, HUNT = { u: 'U', d: 'D', l: 'L', r: 'R' };
  const SIGHT = 6;                                               // how many cells away a hunter can spot the hero
  const k = (r, c) => r + ',' + c;                               // the string key for cell (r, c)

  /**
   * Turn the list of row strings into { L, start }.
   *   L     = the part of a room that never changes: size, walls, the exit, the decorative arch.
   *   start = the starting state: hero, blocks, hearts, water and ghosts.
   * Keeping the two apart means a state can be copied cheaply, and a room can be restarted from `start`.
   */
  function parse(rows) {
    const L = { h: rows.length, w: rows[0].length, walls: new Set(), arch: null, exit: null };
    const s = { player: null, blocks: new Set(), hearts: new Set(), water: new Set(), enemies: [], dead: false };
    rows.forEach((row, r) => [...row].forEach((ch, c) => {
      const key = k(r, c);
      if (ch === '#') L.walls.add(key);
      else if (ch === 'N') { L.walls.add(key); L.arch = [r, c]; }          // the arch is a wall that is drawn as a doorway
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

  // A deep copy of a state.  Every move builds a NEW state rather than editing the old one,
  // which is what makes undo (just keep the old states) and the animations (compare old with new) easy.
  const clone = s => ({ player: s.player.slice(), blocks: new Set(s.blocks), hearts: new Set(s.hearts), water: new Set(s.water),
    enemies: s.enemies.map(e => ({ ...e })), dead: s.dead });
  const inB = (L, p) => p[0] >= 0 && p[0] < L.h && p[1] >= 0 && p[1] < L.w;          // is p inside the room?
  const isExit = (L, p) => p[0] === L.exit[0] && p[1] === L.exit[1];

  /**
   * Does a ghost standing at (r, c) see the hero?  Returns the direction it would look ('U','D','L','R'), or null.
   * The hero is seen only along the SAME row or column, within SIGHT cells, with nothing in between.
   * Walls, emerald blocks and the exit door block the view.  Water and other ghosts do NOT.
   * (Only hunting ghosts act on this; the renderer also uses it to show the "!" above an alerted hunter.)
   */
  function sees(L, s, r, c) {
    const [pr, pc] = s.player;
    if (r === pr && c === pc) return null;                       // same cell: that is a capture, not a sighting
    let d, dist;
    if (r === pr) { d = pc > c ? 'R' : 'L'; dist = Math.abs(pc - c); }
    else if (c === pc) { d = pr > r ? 'D' : 'U'; dist = Math.abs(pr - r); }
    else return null;                                            // not in line: cannot see
    if (dist > SIGHT) return null;
    const [dr, dc] = D[d];
    for (let i = 1; i < dist; i++) {                             // check every cell strictly between ghost and hero
      const q = [r + dr * i, c + dc * i];
      if (L.walls.has(k(q[0], q[1])) || s.blocks.has(k(q[0], q[1])) || isExit(L, q)) return null;
    }
    return d;
  }

  /**
   * The world's turn: every ghost takes one step, in order.  Runs after each hero move AND after a wait.
   *   - A hunter that sees the hero turns to face them and steps toward them.
   *   - Otherwise (patrollers, or hunters that see nothing) the ghost walks the way it faces,
   *     and turns round if its next cell is blocked.
   *   - A ghost cannot enter walls, water, blocks, the exit, the edge of the room or another ghost.
   * If a ghost lands on the hero the state is marked dead and we stop immediately.
   */
  function worldTurn(L, s) {
    const n = clone(s);
    for (let i = 0; i < n.enemies.length; i++) {
      const e = n.enemies[i];
      // Can ghost i step into q?  (Ghosts earlier in the list have already moved; later ones have not.)
      const free = q => inB(L, q) && !L.walls.has(k(q[0], q[1])) && !n.water.has(k(q[0], q[1])) && !n.blocks.has(k(q[0], q[1]))
        && !isExit(L, q) && !n.enemies.some((o, j) => j !== i && o.r === q[0] && o.c === q[1]);
      const sd = e.hunter ? sees(L, n, e.r, e.c) : null;
      if (sd) {
        e.d = sd; const q = [e.r + D[sd][0], e.c + D[sd][1]];
        if (free(q)) { e.r = q[0]; e.c = q[1]; }
      } else {
        const q = [e.r + D[e.d][0], e.c + D[e.d][1]];
        if (free(q)) { e.r = q[0]; e.c = q[1]; } else e.d = OPP[e.d];   // blocked: turn round (no step this turn)
      }
      if (e.r === n.player[0] && e.c === n.player[1]) { n.dead = true; return n; }
    }
    return n;
  }

  /**
   * Apply one action to a state.  `a` is 'U','D','L','R' (move/push) or 'S' (wait).
   * Returns { state, moved, ... } where:
   *   moved  - false when nothing happened (a bump into a wall is NOT a turn, so the ghosts do not move)
   *   state  - the new state (the very same object `s` when nothing happened)
   *   locked - true when the hero tried to enter the exit while hearts remain
   *   waited / pushed - what kind of move it was (the renderer animates these differently)
   *   event  - 'heart' | 'open' (last heart taken) | 'splash' (block fills water) | 'win' | 'dead'
   *   at     - where the event happened, for the little heart / splash effects
   */
  function step(L, s, a) {
    const none = { state: s, moved: false };
    if (s.dead || isExit(L, s.player)) return none;               // the attempt is over: no more moves
    if (a === 'S') return { state: worldTurn(L, s), moved: true, waited: true };   // waiting is a real turn
    const [dr, dc] = D[a];
    const t = [s.player[0] + dr, s.player[1] + dc], tk = k(t[0], t[1]);            // t = the cell we want to enter
    if (!inB(L, t) || L.walls.has(tk) || s.water.has(tk)) return none;             // walls and open water stop the hero
    const n = clone(s);
    if (isExit(L, t)) {
      if (s.hearts.size) return { state: s, moved: false, locked: true };          // door is shut until every heart is taken
      n.player = t; return { state: n, moved: true, event: 'win' };                // stepping in ends the room (no ghost turn)
    }
    const info = { moved: true };
    if (s.blocks.has(tk)) {
      // Pushing a block: it slides one cell further (u).  It cannot go into a wall, the exit, another block,
      // a heart or a ghost.  If u is water, the block and the water both vanish and the way is bridged.
      const u = [t[0] + dr, t[1] + dc], uk = k(u[0], u[1]);
      if (!inB(L, u) || L.walls.has(uk) || isExit(L, u) || s.blocks.has(uk) || s.hearts.has(uk) || s.enemies.some(e => e.r === u[0] && e.c === u[1])) return none;
      n.blocks.delete(tk); n.player = t; info.pushed = true;
      if (s.water.has(uk)) { n.water.delete(uk); info.event = 'splash'; info.at = u; } else n.blocks.add(uk);
    } else {
      n.player = t;
      if (n.hearts.delete(tk)) { info.event = n.hearts.size ? 'heart' : 'open'; info.at = t; }   // collected a heart
      // Walking INTO a ghost is fatal, just as being walked into is (checked in worldTurn).
      if (s.enemies.some(e => e.r === t[0] && e.c === t[1])) { n.dead = true; info.event = 'dead'; return { ...info, state: n }; }
    }
    const w = worldTurn(L, n);                                    // after the hero's move, the ghosts move
    if (w.dead) info.event = 'dead';
    return { ...info, state: w };
  }
  window.Engine = { parse, step, clone, sees };
})();
