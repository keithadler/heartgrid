/**
 * game.js - the controller: owns the game state, reads the keyboard, runs the animation loop and
 * the room-to-room transition, and keeps the side panel up to date.  Rules live in engine.js and
 * drawing in render.js; neither knows about the other.
 */
(() => {
  const { Engine, Render, Minimap } = window, LEVELS = window.LEVELS, TILE = Render.TILE;
  const $ = id => document.getElementById(id);
  const canvas = $('cv'), g = canvas.getContext('2d'), mapCanvas = $('map');

  const DR = { U: -1, D: 1, L: 0, R: 0 }, DC = { U: 0, D: 0, L: -1, R: 1 };
  const OPPOSITE = { U: 'D', D: 'U', L: 'R', R: 'L' };
  const KEYS = { ArrowUp: 'U', ArrowDown: 'D', ArrowLeft: 'L', ArrowRight: 'R', w: 'U', s: 'D', a: 'L', d: 'R', ' ': 'S', '.': 'S' };
  const NEXT_ROOM_DELAY_MS = 700, SLIDE_MS = 650, REPLAY_STEP_MS = 150, MAX_BOARD_ZOOM = 1.8;
  const UNLOCK_ALL = /[?&]all/.test(location.search);

  // ---- saved progress: { roomNumber: fewest moves } ----
  const STORAGE_KEY = 'heartgrid2';
  let best = {};
  try { best = JSON.parse(localStorage.getItem(STORAGE_KEY) || '{}'); } catch (e) { /* private mode: play without saving */ }
  const saveBest = () => { try { localStorage.setItem(STORAGE_KEY, JSON.stringify(best)); } catch (e) { /* ignore */ } };

  // ---- everything that changes while playing lives in `game` ----
  const game = {
    index: 0,            // which room
    room: null,          // parsed room { L, start }
    state: null,         // current Engine state
    history: [],         // earlier states, for undo
    moves: 0,
    won: false, dead: false, finished: false,
    facing: 'D',
    anim: null,          // last move's animation info (see act())
    effects: [],         // floating hearts / splashes
    message: '',
    replay: null,        // timer id while the proof replay runs
    transition: null,    // { t0, dir, image } while sliding between rooms
  };
  let pixelRatio = 1;    // canvas pixels per logical unit

  // ---------------------------------------------------------------- loading a room

  function loadRoom(index, from) {
    const lv = LEVELS[index];
    clearTimeout(game.replay); game.replay = null;
    Object.assign(game, {
      index, room: Engine.parse(lv.rows), history: [], moves: 0,
      won: false, dead: false, message: '', anim: null, effects: [],
    });
    game.state = Engine.clone(game.room.start);
    game.transition = from ? { t0: performance.now(), dir: from.dir, image: from.image } : null;
    $('title').textContent = `Room ${lv.n}: ${lv.name}`;
    const how = lv.proof === 'kernel' ? 'kernel-checked' : 'exhaustive search run as compiled code (native_decide)';
    $('proof').innerHTML = `✔ Proven in Lean 4<br>Solvable in <b>${lv.opt}</b> moves (kernel-checked), and <b>no fewer</b> is possible – ${how}.` +
      `<br><code>HeartGrid.L${lv.n}_solves · L${lv.n}_min</code>`;
    fitCanvas(); refresh();
  }

  /** Size the canvas: crisp (enough pixels) and as large as the window allows. */
  function fitCanvas() {
    const { L } = game.room, w = L.w * TILE, h = L.h * TILE;
    const room = $('board').clientWidth - 20, tall = innerHeight - 150;
    const zoom = Math.max(.4, Math.min(room / w, tall / h, MAX_BOARD_ZOOM));
    pixelRatio = window.HG_SCALE || Math.max(1, Math.ceil(zoom * (window.devicePixelRatio || 1)));
    canvas.width = Math.round(w * pixelRatio); canvas.height = Math.round(h * pixelRatio);
    canvas.style.width = Math.round(w * zoom) + 'px'; canvas.style.height = Math.round(h * zoom) + 'px';
  }

  function refresh() {
    $('moves').textContent = game.moves;
    $('hearts').textContent = game.state.hearts.size;
    const fewest = best[LEVELS[game.index].n];
    $('best').textContent = fewest ? `${fewest} (optimal ${LEVELS[game.index].opt})` : '–';
    $('msg').textContent = game.message;
    $('undo').disabled = !game.history.length || !!game.replay;
    Minimap.draw(mapCanvas, LEVELS, game.index, n => !!best[n]);
  }

  // ---------------------------------------------------------------- playing

  /** Try one action ('U','D','L','R' or 'S' = wait).  Returns whether anything happened. */
  function act(action) {
    if (game.won || game.dead || game.transition) return false;
    const result = Engine.step(game.room.L, game.state, action);
    if (result.locked) { game.message = 'The door is sealed – collect every heart first.'; refresh(); return false; }
    if (!result.moved) return false;

    const before = game.state;
    game.history.push(before); game.state = result.state; game.moves++; game.message = '';
    if (action !== 'S') game.facing = action;
    game.anim = { t0: performance.now(), d: action, waited: result.waited, pushed: result.pushed,
                  prevBlocks: before.blocks, prevEnemies: before.enemies, prevPlayer: before.player };

    const now = performance.now();
    if (result.event === 'splash') game.effects.push({ at: result.at, t0: now, kind: 'splash' });
    if (result.event === 'heart' || result.event === 'open') game.effects.push({ at: result.at, t0: now, kind: 'heart' });
    if (result.event === 'open') game.message = 'The door opens!';
    if (game.state.dead) { game.dead = true; game.message = 'Caught! Press Z to undo or R to restart.'; }
    if (result.event === 'win') onWin();
    refresh(); return true;
  }

  function onWin() {
    game.won = true;
    const lv = LEVELS[game.index], perfect = game.moves === lv.opt;
    game.message = perfect ? `Perfect – ${game.moves} moves, the proven optimum!` : `Cleared in ${game.moves} (optimum ${lv.opt}).`;
    if (game.replay) return;                          // a proof replay does not count as a score
    if (!best[lv.n] || game.moves < best[lv.n]) { best[lv.n] = game.moves; saveBest(); }
    setTimeout(nextRoom, NEXT_ROOM_DELAY_MS);
  }

  /** Walk through the door: slide the old room out and the next one in. */
  function nextRoom() {
    if (!game.won) return;
    if (game.index + 1 >= LEVELS.length) { game.finished = true; game.message = 'You have crossed every proven room!'; refresh(); return; }
    const dir = OPPOSITE[LEVELS[game.index + 1].enter] || 'R';
    const image = new Image();
    image.onload = () => loadRoom(game.index + 1, { dir, image });
    image.src = canvas.toDataURL();
  }

  function undo() {
    if (!game.history.length || game.replay || game.transition) return;
    game.state = game.history.pop(); game.moves--; game.won = game.dead = false; game.anim = null; game.message = '';
    refresh();
  }
  const restart = () => { if (!game.transition) loadRoom(game.index); };

  /** Replay the Lean-verified optimal solution move by move. */
  function showProof() {
    if (game.transition) return;
    loadRoom(game.index);
    const solution = LEVELS[game.index].sol; let i = 0;
    game.message = 'Replaying the Lean-verified solution…';
    const tick = () => {
      if (i >= solution.length) { game.replay = null; return; }
      act(solution[i++]); game.message = '';
      game.replay = setTimeout(tick, REPLAY_STEP_MS);
    };
    game.replay = setTimeout(tick, 0);
  }

  // ---------------------------------------------------------------- input

  addEventListener('keydown', e => {
    if (KEYS[e.key]) { e.preventDefault(); if (!game.replay) act(KEYS[e.key]); }
    else if (e.key === 'z' || e.key === 'Z') undo();
    else if (e.key === 'r' || e.key === 'R') restart();
    else if (e.key === 'Enter' && game.won) nextRoom();
  });
  addEventListener('resize', () => { fitCanvas(); });
  $('undo').onclick = undo; $('reset').onclick = restart; $('hint').onclick = showProof;
  $('wait').onclick = () => { if (!game.replay) act('S'); };
  document.querySelectorAll('#pad button').forEach(b => b.onclick = () => { if (!game.replay) act(b.dataset.d); });
  mapCanvas.onclick = event => {      // jump to any room you have already reached
    const i = Minimap.hit(mapCanvas, LEVELS, event);
    if (i >= 0 && (UNLOCK_ALL || i === 0 || best[LEVELS[i - 1].n])) loadRoom(i);
  };

  // ---------------------------------------------------------------- frame loop

  function currentBanner() {
    if (game.dead) return { title: 'Caught!', subtitle: 'Z to undo · R to restart' };
    if (game.finished) return { title: 'Every room cleared!', subtitle: 'All proven in Lean 4' };
    return null;
  }

  function frame(now) {
    game.effects = game.effects.filter(f => now - f.t0 < 450);
    g.setTransform(pixelRatio, 0, 0, pixelRatio, 0, 0);
    Render.drawRoom(g, { room: game.room, state: game.state, anim: game.anim, effects: game.effects,
                         facing: game.facing, dead: game.dead, banner: currentBanner() }, now);
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
