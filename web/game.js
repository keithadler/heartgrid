/**
 * game.js - the controller: owns the game state, reads the keyboard, runs the animation loop and
 * the room-to-room transition, and keeps the side panel up to date.  Rules live in engine.js and
 * drawing in render.js; neither knows about the other.
 */
(() => {
  const { Engine, Render, Minimap } = window, LEVELS = window.LEVELS, TILE = Render.TILE;
  const $ = id => document.getElementById(id);
  const canvas = $('cv'), g = canvas.getContext('2d'), mapCanvas = $('map'), chart = $('chart');

  const DR = { U: -1, D: 1, L: 0, R: 0 }, DC = { U: 0, D: 0, L: -1, R: 1 };
  const OPPOSITE = { U: 'D', D: 'U', L: 'R', R: 'L' };
  const ARROW = { U: '↑', D: '↓', L: '←', R: '→', S: '·' };
  const KEYS = { ArrowUp: 'U', ArrowDown: 'D', ArrowLeft: 'L', ArrowRight: 'R', w: 'U', s: 'D', a: 'L', d: 'R', ' ': 'S', '.': 'S' };
  const SLIDE_MS = 650, REPLAY_STEP_MS = 400, MAX_BOARD_ZOOM = 1.8, TRIES_BEFORE_SOLUTION = 2, SWIPE_PX = 24;
  const UNLOCK_ALL = /[?&]all/.test(location.search);
  const REDUCED = !!(window.matchMedia && matchMedia('(prefers-reduced-motion: reduce)').matches);

  // ---- saved progress ----
  const store = {
    read(key, fallback) { try { return JSON.parse(localStorage.getItem(key) || 'null') || fallback; } catch (e) { return fallback; } },
    write(key, value) { try { localStorage.setItem(key, JSON.stringify(value)); } catch (e) { /* private mode: play without saving */ } },
  };
  const best = store.read('heartgrid2', {});                 // { roomNumber: fewest moves }
  const revealed = new Set(store.read('heartgrid2r', []));   // rooms whose shortest length has been shown
  const tries = {};                                          // this visit: failed or restarted attempts per room
  const known = n => UNLOCK_ALL || revealed.has(n) || !!best[n];

  const game = {
    index: 0, room: null, state: null, history: [], moves: 0, log: [],
    won: false, dead: false, finished: false, facing: 'D',
    guess: null, bound: 0,
    axes: 0,             // 0 off, 1 label cells, 2 label grid lines
    hover: null, logPoints: false, fit: false,
    anim: null, effects: [], message: '',
    replay: null,        // { timer, i, paused, sol } while the shortest solution plays
    transition: null,
  };
  let pixelRatio = 1;

  /** Fewest moves any route could take, ignoring walls, blocks and ghosts: the shortest tour
   *  start -> every heart (best order) -> door, measured in whole steps along rows and columns. */
  function distanceBound(room) {
    const [er, ec] = room.L.exit, hearts = [...room.start.hearts].map(k => k.split(',').map(Number));
    const dist = (a, b) => Math.abs(a[0] - b[0]) + Math.abs(a[1] - b[1]);
    let bestLen = Infinity;
    const walk = (at, left, len) => {
      if (len >= bestLen) return;
      if (!left.length) { bestLen = Math.min(bestLen, len + dist(at, [er, ec])); return; }
      left.forEach((h, i) => walk(h, left.filter((_, j) => j !== i), len + dist(at, h)));
    };
    walk(room.start.player, hearts, 0);
    return bestLen;
  }
  const gcd = (a, b) => b ? gcd(b, a % b) : a;
  const announce = text => { $('sr').textContent = ''; setTimeout(() => { $('sr').textContent = text; }, 30); };

  // ---------------------------------------------------------------- loading a room

  function loadRoom(index, from) {
    const lv = LEVELS[index];
    if (game.replay) clearTimeout(game.replay.timer);
    Object.assign(game, {
      index, room: Engine.parse(lv.rows), history: [], moves: 0, log: [], guess: null, replay: null,
      won: false, dead: false, message: '', anim: null, effects: [],
    });
    game.bound = distanceBound(game.room);
    game.state = Engine.clone(game.room.start);
    game.transition = from && !REDUCED ? { t0: performance.now(), dir: from.dir, image: from.image } : null;
    $('title').textContent = `Room ${lv.n}: ${lv.name}`;
    $('guessIn').value = '';
    $('about').innerHTML = `The shortest-length claims were checked with the Lean 4 proof assistant against the rules in ` +
      `<code>HeartGrid/Rules.lean</code> (this room: <code>L${lv.n}_solves</code>, <code>L${lv.n}_min</code>). ` +
      `This page runs a separate JavaScript copy of those rules, kept in step by tests. ` +
      (lv.proof === 'kernel' ? 'This room’s search was checked by the Lean kernel.' : 'This room’s search ran as compiled code, which also trusts the Lean compiler.');
    fitCanvas(); refresh();
  }

  function fitCanvas() {
    const { L } = game.room, w = L.w * TILE, h = L.h * TILE;
    const room = $('board').clientWidth - 20, tall = innerHeight - 150;
    const zoom = Math.max(.4, Math.min(room / w, tall / h, MAX_BOARD_ZOOM));
    pixelRatio = window.HG_SCALE || Math.max(1, Math.ceil(zoom * (window.devicePixelRatio || 1)));
    canvas.width = Math.round(w * pixelRatio); canvas.height = Math.round(h * pixelRatio);
    canvas.style.width = Math.round(w * zoom) + 'px'; canvas.style.height = Math.round(h * zoom) + 'px';
  }

  // ---------------------------------------------------------------- side panel

  const cellOf = (r, c) => `(${c}, ${game.room.L.h - 1 - r})`;
  const canSeeSolution = () => UNLOCK_ALL || !!best[LEVELS[game.index].n] || (tries[game.index] || 0) >= TRIES_BEFORE_SOLUTION;

  function refresh() {
    const lv = LEVELS[game.index], [pr, pc] = game.state.player, [sr, sc] = game.room.start.player;
    const show = known(lv.n) || game.won;
    $('moves').textContent = game.moves;
    $('hearts').textContent = game.state.hearts.size;
    $('best').textContent = best[lv.n] ? `${best[lv.n]}` : '–';
    $('pos').textContent = cellOf(pr, pc);
    $('net').textContent = `Δx ${pc - sc}, Δy ${sr - pr}`;
    $('msg').textContent = game.message;

    // moves so far : shortest, then (after the room) shortest : yours as ratio, fraction, decimal and percent
    if (show && game.moves > 0) {
      if (game.won) {
        const d = gcd(lv.opt, game.moves);
        $('ratioLabel').textContent = 'Shortest : yours';
        $('ratio').textContent = `${lv.opt} : ${game.moves} = ${lv.opt / d}/${game.moves / d} ≈ ${(lv.opt / game.moves).toFixed(2)} = ${Math.round(100 * lv.opt / game.moves)}%`;
      } else {
        $('ratioLabel').textContent = 'Moves so far : shortest';
        $('ratio').textContent = `${game.moves} : ${lv.opt}`;
      }
    } else { $('ratioLabel').textContent = 'Moves : shortest'; $('ratio').textContent = '–'; }

    $('guess').hidden = !(game.moves === 0 && game.guess === null && !show);
    $('reveal').hidden = show;
    $('proof').hidden = !show;
    if (show) {
      $('proof').innerHTML = `Shortest possible: <b>${lv.opt}</b> moves.<br>Straight-line distance bound: <b>${game.bound}</b>. ` +
        `Walls, blocks and ghosts account for the other <b>${lv.opt - game.bound}</b>.`;
    }
    $('result').hidden = !game.won;
    if (game.won) {
      const g1 = game.guess === null ? '' : `Your guess: <b>${game.guess}</b> · `;
      $('result').innerHTML = `${g1}Distance bound: <b>${game.bound}</b> · Your moves: <b>${game.moves}</b> · Shortest: <b>${lv.opt}</b>` +
        (game.guess === null ? '' : `<br>Guess was off by <b>${Math.abs(game.guess - game.moves)}</b> from your moves.`);
    }

    const replaying = !!game.replay;
    $('undo').disabled = !game.history.length || replaying;
    $('hint').disabled = replaying || !canSeeSolution();
    $('pause').hidden = $('stepBtn').hidden = !replaying;
    $('pause').textContent = replaying && game.replay.paused ? 'Play' : 'Pause';
    $('stepBtn').disabled = !(replaying && game.replay.paused);
    $('next').hidden = !(game.won && !game.finished);
    $('note').textContent = canSeeSolution() ? '' : 'The shortest solution unlocks after you clear this room or try it twice.';
    $('axes').setAttribute('aria-pressed', String(game.axes > 0));
    $('axes').textContent = ['Grid (G)', 'Grid: cells (G)', 'Grid: lines (G)'][game.axes];
    $('axes').classList.toggle('axes-on', game.axes > 0);
    canvas.setAttribute('aria-label', `Room ${lv.n}. You are on cell ${cellOf(pr, pc)}. ${game.state.hearts.size} hearts left. ` +
      (game.state.hearts.size ? 'The door is shut.' : 'The door is open.'));

    renderLog();
    renderTable();
    Minimap.draw(mapCanvas, LEVELS, game.index, n => !!best[n]);
  }

  function renderLog() {
    $('logMode').textContent = game.logPoints ? 'Show as arrows' : 'Show as points';
    if (game.logPoints) {
      const path = game.history.map(s => s.player).concat([game.state.player]);
      $('log').textContent = path.map(p => cellOf(p[0], p[1])).join(' → ');
    } else $('log').textContent = game.log.map(a => ARROW[a]).join(' ') || '–';
    $('log').scrollTop = 1e6;
    const n = d => game.log.filter(a => a === d).length;
    $('tally').textContent = game.log.length ? `→ ${n('R')}   ← ${n('L')}   ↑ ${n('U')}   ↓ ${n('D')}   waits ${n('S')}` : '';
  }

  /** Shortest-length table, the first differences, and the plot - only for rooms whose length is known. */
  function renderTable() {
    $('seq').tBodies[0].innerHTML = LEVELS.map((l, i) => {
      const prev = LEVELS[i - 1], diff = i && known(l.n) && known(prev.n) ? '+' + (l.opt - prev.opt) : '';
      return `<tr${i === game.index ? ' class="cur"' : ''}><td>${l.n}</td><td>${known(l.n) ? l.opt : '?'}</td><td>${diff}</td><td>${best[l.n] || '–'}</td></tr>`;
    }).join('');
    $('chain').textContent = LEVELS.map(l => known(l.n) ? l.opt : '?').join(' < ');
    drawChart();
  }

  function drawChart() {
    const c = chart.getContext('2d'), W = chart.width, H = chart.height, m = { l: 30, r: 8, t: 8, b: 20 };
    const maxN = LEVELS.length, maxY = Math.max(...LEVELS.map(l => l.opt)), X = n => m.l + (n - 1) / (maxN - 1) * (W - m.l - m.r),
      Y = v => H - m.b - v / maxY * (H - m.t - m.b);
    c.clearRect(0, 0, W, H); c.font = '10px system-ui'; c.fillStyle = c.strokeStyle = '#c9c3e6'; c.lineWidth = 1;
    c.beginPath(); c.moveTo(m.l, m.t); c.lineTo(m.l, H - m.b); c.lineTo(W - m.r, H - m.b); c.stroke();
    c.textAlign = 'center'; for (let n = 1; n <= maxN; n += 1) if (n % 2 || n === maxN) c.fillText(n, X(n), H - 6);
    c.textAlign = 'right'; for (let v = 0; v <= maxY; v += 40) c.fillText(v, m.l - 4, Y(v) + 3);
    const pts = LEVELS.filter(l => known(l.n)).map(l => [l.n, l.opt]);
    c.fillStyle = '#ff5d8f'; pts.forEach(([n, v]) => { c.beginPath(); c.arc(X(n), Y(v), 3.5, 0, 7); c.fill(); });
    c.strokeStyle = '#5ee0a0'; c.lineWidth = 2;
    LEVELS.filter(l => best[l.n]).forEach(l => { c.beginPath(); c.arc(X(l.n), Y(best[l.n]), 5.5, 0, 7); c.stroke(); });
    let text = pts.length ? 'Pink dots: shortest possible. Green rings: your best.' : 'Reveal or clear a room to plot its shortest length.';
    if (game.fit && pts.length >= 2) {
      const n = pts.length, sx = pts.reduce((a, p) => a + p[0], 0), sy = pts.reduce((a, p) => a + p[1], 0);
      const sxy = pts.reduce((a, p) => a + p[0] * p[1], 0), sxx = pts.reduce((a, p) => a + p[0] * p[0], 0);
      const slope = (n * sxy - sx * sy) / (n * sxx - sx * sx), icpt = (sy - slope * sx) / n;
      c.strokeStyle = '#ffe14a'; c.lineWidth = 1.5; c.beginPath();
      c.moveTo(X(1), Y(slope + icpt)); c.lineTo(X(maxN), Y(slope * maxN + icpt)); c.stroke();
      text += ` Line: moves ≈ ${slope.toFixed(1)} × room + ${icpt.toFixed(1)} (about ${slope.toFixed(1)} more moves per room).`;
    }
    $('fit').textContent = text;
    $('fitBtn').setAttribute('aria-pressed', String(game.fit));
    $('fitBtn').textContent = game.fit ? 'Hide line of best fit' : 'Show line of best fit';
  }

  // ---------------------------------------------------------------- playing

  /** Try one action ('U','D','L','R' or 'S' = wait).  Returns whether anything happened. */
  function act(action) {
    if (game.won || game.dead || game.transition) return false;
    const result = Engine.step(game.room.L, game.state, action);
    if (result.locked) { game.message = 'The door is sealed – collect every heart first.'; announce(game.message); refresh(); return false; }
    if (!result.moved) return false;

    const before = game.state;
    game.history.push(before); game.state = result.state; game.moves++; game.log.push(action); game.message = '';
    if (action !== 'S') game.facing = action;
    game.anim = { t0: performance.now(), d: action, waited: result.waited, pushed: result.pushed,
                  prevBlocks: before.blocks, prevEnemies: before.enemies, prevPlayer: before.player };

    const now = performance.now();
    if (result.event === 'splash') { game.effects.push({ at: result.at, t0: now, kind: 'splash' }); announce('The block fills the water.'); }
    if (result.event === 'heart' || result.event === 'open') {
      game.effects.push({ at: result.at, t0: now, kind: 'heart' });
      announce(`Heart collected, ${game.state.hearts.size} left.`);
    }
    if (result.event === 'open') { game.message = 'The door opens!'; announce('The door opens!'); }
    if (game.state.dead) {
      game.dead = true; game.message = 'Caught! Press Z to undo or R to restart.'; announce('Caught!');
      if (!game.replay) tries[game.index] = (tries[game.index] || 0) + 1;
    }
    if (result.event === 'win') onWin();
    refresh(); return true;
  }

  function onWin() {
    game.won = true;
    const lv = LEVELS[game.index], perfect = game.moves === lv.opt;
    game.message = perfect ? `Perfect run – ${game.moves} moves, the shortest possible!` : `Cleared in ${game.moves} moves (shortest possible: ${lv.opt}).`;
    announce(game.message);
    if (game.replay) return;                          // a replay does not count as a score
    if (!best[lv.n] || game.moves < best[lv.n]) { best[lv.n] = game.moves; store.write('heartgrid2', best); }
    revealed.add(lv.n); store.write('heartgrid2r', [...revealed]);
  }

  /** Walk through the door: slide the old room out and the next one in. */
  function nextRoom() {
    if (!game.won || game.transition) return;
    if (game.index + 1 >= LEVELS.length) { game.finished = true; game.message = 'You have crossed every room!'; refresh(); return; }
    const dir = OPPOSITE[LEVELS[game.index + 1].enter] || 'R';
    const image = new Image();
    image.onload = () => loadRoom(game.index + 1, { dir, image });
    image.src = canvas.toDataURL();
  }

  function undo() {
    if (!game.history.length || game.replay || game.transition) return;
    game.state = game.history.pop(); game.moves--; game.log.pop(); game.won = game.dead = false; game.anim = null; game.message = '';
    refresh();
  }
  function restart() {
    if (game.transition) return;
    if (game.moves > 0 && !game.won && !game.dead && !game.replay) tries[game.index] = (tries[game.index] || 0) + 1;
    loadRoom(game.index);
  }

  function revealOptimum() {
    const n = LEVELS[game.index].n;
    revealed.add(n); store.write('heartgrid2r', [...revealed]); refresh();
  }
  function lockGuess() {
    const v = parseInt($('guessIn').value, 10);
    if (!(v >= 0)) { $('guessIn').focus(); return; }
    game.guess = v; game.message = `Guess locked in: ${v} moves.`; refresh(); canvas.focus();
  }

  /** Replay the shortest solution, with pause and single-step. */
  function showSolution() {
    if (game.transition || !canSeeSolution()) return;
    revealOptimum();
    loadRoom(game.index);
    game.replay = { timer: null, i: 0, paused: false, sol: LEVELS[game.index].sol };
    game.message = 'Replaying the shortest solution…';
    refresh(); scheduleReplay(0);
  }
  function scheduleReplay(delay) {
    const r = game.replay; if (!r) return;
    clearTimeout(r.timer);
    r.timer = setTimeout(() => { stepReplay(); if (game.replay && !game.replay.paused) scheduleReplay(REPLAY_STEP_MS); }, delay);
  }
  function stepReplay() {
    const r = game.replay; if (!r) return;
    if (r.i >= r.sol.length) { game.replay = null; refresh(); return; }
    act(r.sol[r.i++]); game.message = '';
    if (r.i >= r.sol.length) { game.replay = null; refresh(); }
  }
  function pauseReplay() {
    const r = game.replay; if (!r) return;
    r.paused = !r.paused; clearTimeout(r.timer);
    if (!r.paused) scheduleReplay(0);
    refresh();
  }

  const cycleAxes = () => { game.axes = (game.axes + 1) % 3; refresh(); };

  // ---------------------------------------------------------------- input

  addEventListener('keydown', e => {
    if (e.ctrlKey || e.metaKey || e.altKey) return;                  // leave browser shortcuts alone
    const tag = e.target.tagName;
    if (tag === 'INPUT' || tag === 'SELECT' || tag === 'TEXTAREA') {
      if (tag === 'INPUT' && e.key === 'Enter') lockGuess();
      return;
    }
    if (tag === 'BUTTON' && (e.key === ' ' || e.key === 'Enter')) return;   // let the focused button take it
    if (KEYS[e.key]) { e.preventDefault(); if (!game.replay) act(KEYS[e.key]); }
    else if (e.key === 'z' || e.key === 'Z') undo();
    else if (e.key === 'r' || e.key === 'R') restart();
    else if (e.key === 'g' || e.key === 'G') cycleAxes();
    else if (e.key === 'Enter' && game.won) nextRoom();
  });
  addEventListener('resize', () => { fitCanvas(); });
  $('undo').onclick = undo; $('reset').onclick = restart; $('hint').onclick = showSolution; $('axes').onclick = cycleAxes;
  $('next').onclick = nextRoom; $('pause').onclick = pauseReplay; $('stepBtn').onclick = stepReplay;
  $('lock').onclick = lockGuess; $('revealBtn').onclick = revealOptimum;
  $('wait').onclick = () => { if (!game.replay) act('S'); };
  $('logMode').onclick = () => { game.logPoints = !game.logPoints; renderLog(); };
  $('fitBtn').onclick = () => { game.fit = !game.fit; drawChart(); };
  document.querySelectorAll('#pad button').forEach(b => b.onclick = () => {
    if (b.dataset.act === 'undo') undo(); else if (!game.replay) act(b.dataset.d);
  });
  mapCanvas.onclick = event => {      // jump to any room you have already reached
    const i = Minimap.hit(mapCanvas, LEVELS, event);
    if (i >= 0 && (UNLOCK_ALL || i === 0 || best[LEVELS[i - 1].n])) loadRoom(i);
  };

  // pointer: show which cell it is over (hover on a mouse, tap on a touch screen), swipe to move
  function cellAt(e) {
    const { L } = game.room, b = canvas.getBoundingClientRect();
    const c = Math.floor((e.clientX - b.left) / b.width * L.w), r = Math.floor((e.clientY - b.top) / b.height * L.h);
    return r >= 0 && c >= 0 && r < L.h && c < L.w ? [r, c] : null;
  }
  const showPointer = cell => { game.hover = cell; $('ptr').textContent = cell ? cellOf(cell[0], cell[1]) : '–'; };
  canvas.onmousemove = e => showPointer(cellAt(e));
  canvas.onmouseleave = () => showPointer(null);
  canvas.onclick = e => showPointer(cellAt(e));
  let touch0 = null;
  canvas.addEventListener('touchstart', e => { touch0 = e.touches[0]; }, { passive: true });
  canvas.addEventListener('touchend', e => {
    if (!touch0 || game.replay) return;
    const t = e.changedTouches[0], dx = t.clientX - touch0.clientX, dy = t.clientY - touch0.clientY; touch0 = null;
    if (Math.max(Math.abs(dx), Math.abs(dy)) < SWIPE_PX) return;
    act(Math.abs(dx) > Math.abs(dy) ? (dx > 0 ? 'R' : 'L') : (dy > 0 ? 'D' : 'U'));
  });

  // ---------------------------------------------------------------- frame loop

  function currentBanner() {
    if (game.dead) return { title: 'Caught!', subtitle: 'Z to undo · R to restart' };
    if (game.finished) return { title: 'Every room cleared!', subtitle: 'Nicely done' };
    return null;
  }

  function frame(now) {
    game.effects = game.effects.filter(f => now - f.t0 < 450);
    g.setTransform(pixelRatio, 0, 0, pixelRatio, 0, 0);
    Render.drawRoom(g, { room: game.room, state: game.state, anim: REDUCED ? null : game.anim, effects: REDUCED ? [] : game.effects,
                         facing: game.facing, axes: game.axes, hover: game.hover, dead: game.dead, banner: currentBanner() }, now);
    if (game.transition) drawTransition(now);
    requestAnimationFrame(frame);
  }

  /** Room-to-room slide: the old room leaves the way we walked and the new one arrives behind it. */
  function drawTransition(now) {
    const t = game.transition, W = canvas.width, H = canvas.height;
    const p = Math.min(1, (now - t.t0) / SLIDE_MS), ease = 1 - Math.pow(1 - p, 3);
    const dx = DC[t.dir] * W, dy = DR[t.dir] * H;
    const incoming = document.createElement('canvas'); incoming.width = W; incoming.height = H;
    incoming.getContext('2d').drawImage(canvas, 0, 0);
    g.setTransform(1, 0, 0, 1, 0, 0);
    g.fillStyle = '#14121f'; g.fillRect(0, 0, W, H);
    g.drawImage(t.image, -dx * ease, -dy * ease, W, H);
    g.drawImage(incoming, dx * (1 - ease), dy * (1 - ease));
    if (p >= 1) game.transition = null;
  }

  // ---------------------------------------------------------------- start
  let first = 0;
  while (!UNLOCK_ALL && first + 1 < LEVELS.length && best[LEVELS[first].n]) first++;
  loadRoom(first);
  requestAnimationFrame(frame);
})();
