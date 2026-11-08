/**
 * render.js - draws one room onto a 2D canvas context.
 *
 * Pure drawing: it reads a `view` object and paints it, and never changes game state.
 * Everything is drawn in "logical" units where one tile is `TILE` (48) units wide; the caller
 * scales the context (see game.js) so the picture stays crisp at any size or pixel density.
 *
 * view = {
 *   room:    parsed room from Engine.parse(),         // { L, start }
 *   state:   current game state,
 *   anim:    last move's animation info or null,      // see game.js
 *   effects: [{ at:[r,c], t0, kind:'heart'|'splash' }],
 *   facing:  'U'|'D'|'L'|'R',                         // where the hero is looking
 *   dead:    boolean,
 *   banner:  null | { title, subtitle },              // overlay text
 * }
 */
(function () {
  const TILE = 48;          // logical size of one grid cell; everything below is drawn in these units
  const SLIDE_MS = 120;     // how long a move animation lasts
  const EFFECT_MS = 450;    // how long a heart / splash effect lasts
  // Row / column step for each direction (same idea as engine.js), used to slide things during animations.
  const DR = { U: -1, D: 1, L: 0, R: 0 }, DC = { U: 0, D: 0, L: -1, R: 1 };

  // The whole palette in one place, so the look can be changed without hunting through drawing code.
  const COLOR = {
    floorA: '#2b2745', floorB: '#302b4d',
    wall: '#5b4f86', wallTop: '#7a6cb0', wallShade: '#463b6e', arch: '#1a1630',
    water: '#1d5fa8', ripple: '#6fb6ff',
    heart: '#ff3d77', heartShine: '#ffb3cb',
    blockMid: '#0f8f5a', blockLight: '#34e0a0', blockDark: '#0a6b43', blockCore: '#b8ffe0',
    doorShut: '#7a4a1e', doorShutPanel: '#a8672b', doorShutInner: '#5a3512', doorKnob: '#e8c15a',
    doorOpen: '#ffe9a8', doorOpenInner: '#fff7d6',
    hero: '#4aa3ff', heroShine: '#8ccbff', eye: '#fff', pupil: '#10204a',
    patrol: '#2fb6d6', hunter: '#9a3fd6', enemyPupil: '#1a1030', alert: '#ffe14a',
  };

  // Top-left pixel (x, y) of the cell at row r, column c.  Note the swap: x comes from the column, y from the row.
  const cell = (r, c) => [c * TILE, r * TILE];

  /** A heart shape centred on (cx, cy) with overall size `s`. */
  function heartShape(g, cx, cy, s, fill) {
    const t = s / 2;                       // half the size: the curves below are measured from the centre
    g.fillStyle = fill;
    g.beginPath();
    g.moveTo(cx, cy + t * .9);             // start at the bottom point of the heart
    // Two curves: up the left side over the left lobe and down into the notch at the top middle ...
    g.bezierCurveTo(cx - t * 1.5, cy - t * .1, cx - t * .6, cy - t * 1.1, cx, cy - t * .35);
    // ... and the mirror image on the right, back to the bottom point.
    g.bezierCurveTo(cx + t * .6, cy - t * 1.1, cx + t * 1.5, cy - t * .1, cx, cy + t * .9);
    g.fill();
  }

  function drawHeart(g, cx, cy, s) {
    heartShape(g, cx, cy, s, COLOR.heart);   // the red heart ...

    // ... plus a small pale highlight on the upper left lobe.
    g.fillStyle = COLOR.heartShine;
    g.beginPath(); g.arc(cx - s * .22, cy - s * .15, s * .08, 0, 7); g.fill();
  }

  /** Floor, wall (with the entrance arch) and water for one cell. */
  function drawTerrain(g, view, r, c, now) {
    const { L } = view.room, [x, y] = cell(r, c), key = r + ',' + c;
    // Checkerboard floor: the two floor colours alternate, which also helps the eye count cells.
    g.fillStyle = (r + c) % 2 ? COLOR.floorA : COLOR.floorB;
    g.fillRect(x, y, TILE, TILE);

    if (L.walls.has(key)) {
      // A wall: a block with a light top edge, a dark bottom edge and an outline, so it looks raised.
      g.fillStyle = COLOR.wall; g.fillRect(x, y, TILE, TILE);
      g.fillStyle = COLOR.wallTop; g.fillRect(x, y, TILE, 5);
      g.fillStyle = COLOR.wallShade; g.fillRect(x, y + TILE - 5, TILE, 5);
      g.strokeStyle = COLOR.wallShade; g.strokeRect(x + .5, y + .5, TILE - 1, TILE - 1);
      // The entrance arch: a dark doorway cut into the wall where the hero walked in.
      if (L.arch && L.arch[0] === r && L.arch[1] === c) {
        g.fillStyle = COLOR.arch;
        g.beginPath();
        g.moveTo(x + 8, y + TILE); g.lineTo(x + 8, y + TILE / 2);
        g.arc(x + TILE / 2, y + TILE / 2, TILE / 2 - 8, Math.PI, 0);
        g.lineTo(x + TILE - 8, y + TILE); g.fill();
      }
    }
    if (view.state.water.has(key)) {
      // Water: blue, with two wavy lines whose phase depends on the time `now`, so it ripples.
      g.fillStyle = COLOR.water; g.fillRect(x, y, TILE, TILE);
      g.strokeStyle = COLOR.ripple; g.lineWidth = 2;
      for (let i = 0; i < 2; i++) {
        g.beginPath();
        const yy = y + 14 + i * 18, phase = now / 400 + c + i;
        for (let j = 0; j <= 4; j++) g.lineTo(x + j * (TILE / 4), yy + Math.sin(phase + j) * 3);
        g.stroke();
      }
    }
  }

  /** The exit door: brown and locked until every heart is collected, then bright. */
  function drawDoor(g, view) {
    // The door is open exactly when no hearts are left.
    const [er, ec] = view.room.L.exit, [x, y] = cell(er, ec), open = view.state.hearts.size === 0;
    g.fillStyle = open ? COLOR.floorA : COLOR.doorShut; g.fillRect(x, y, TILE, TILE);
    g.fillStyle = open ? COLOR.doorOpen : COLOR.doorShutPanel; g.fillRect(x + 7, y + 5, TILE - 14, TILE - 5);
    g.fillStyle = open ? COLOR.doorOpenInner : COLOR.doorShutInner; g.fillRect(x + 12, y + 10, TILE - 24, TILE - 10);
    if (!open) { g.fillStyle = COLOR.doorKnob; g.beginPath(); g.arc(x + TILE - 15, y + TILE / 2, 3, 0, 7); g.fill(); }
  }

  /** An emerald block.  r and c may be fractions while it slides, which is why they are not looked up in a grid. */
  function drawBlock(g, r, c) {
    const [x, y] = cell(r, c);
    // Layers: body, light top/left edges, dark bottom/right edges, a bright centre, then a pale outline (a shape cue, not just colour).
    g.fillStyle = COLOR.blockMid; g.fillRect(x + 3, y + 3, TILE - 6, TILE - 6);
    g.fillStyle = COLOR.blockLight; g.fillRect(x + 3, y + 3, TILE - 6, 7); g.fillRect(x + 3, y + 3, 7, TILE - 6);
    g.fillStyle = COLOR.blockDark; g.fillRect(x + TILE - 10, y + 10, 7, TILE - 13); g.fillRect(x + 10, y + TILE - 10, TILE - 13, 7);
    g.fillStyle = COLOR.blockCore; g.fillRect(x + 17, y + 17, 14, 14);
    g.strokeStyle = '#e8fff4'; g.lineWidth = 2; g.strokeRect(x + 4, y + 4, TILE - 8, TILE - 8);   // outline: not colour alone
  }

  /** A ghost: cyan if it only patrols, purple (with angry brows) if it hunts. `!` when it sees you. */
  function drawEnemy(g, view, e, r, c, now) {
    const [x, y] = cell(r, c), cx = x + TILE / 2, cy = y + TILE / 2;
    // A hunter that can see the hero right now shows an animated yellow "!" above its head.
    const alerted = e.hunter && window.Engine.sees(view.room.L, view.state, e.r, e.c);
    g.fillStyle = e.hunter ? COLOR.hunter : COLOR.patrol;
    // Body: a dome on top, straight sides, and a wavy hem along the bottom.
    g.beginPath();
    g.moveTo(cx - 16, cy + 17); g.lineTo(cx - 16, cy - 2); g.arc(cx, cy - 2, 16, Math.PI, 0); g.lineTo(cx + 16, cy + 17);
    for (let i = 0; i < 4; i++) g.lineTo(cx + 16 - (i + .5) * 8, cy + (i % 2 ? 17 : 11));
    g.closePath(); g.fill();
    // Two white eyes, then pupils shifted 2 units toward the direction the ghost is facing.
    g.fillStyle = COLOR.eye; g.beginPath(); g.arc(cx - 6, cy - 3, 5, 0, 7); g.arc(cx + 6, cy - 3, 5, 0, 7); g.fill();
    g.fillStyle = COLOR.enemyPupil;
    const lx = DC[e.d] * 2, ly = DR[e.d] * 2;
    g.beginPath(); g.arc(cx - 6 + lx, cy - 3 + ly, 2.5, 0, 7); g.arc(cx + 6 + lx, cy - 3 + ly, 2.5, 0, 7); g.fill();
    if (e.hunter) {                         // horns: a shape cue, so hunters differ from patrollers without colour
      g.fillStyle = COLOR.hunter;
      g.beginPath(); g.moveTo(cx - 14, cy - 12); g.lineTo(cx - 10, cy - 24); g.lineTo(cx - 4, cy - 15);
      g.moveTo(cx + 14, cy - 12); g.lineTo(cx + 10, cy - 24); g.lineTo(cx + 4, cy - 15); g.fill();
      g.strokeStyle = COLOR.enemyPupil; g.lineWidth = 2; g.beginPath();
      g.moveTo(cx - 12, cy - 11); g.lineTo(cx - 3, cy - 8); g.moveTo(cx + 12, cy - 11); g.lineTo(cx + 3, cy - 8); g.stroke();
    }
    if (alerted) {
      g.fillStyle = COLOR.alert; g.font = 'bold 18px system-ui'; g.textAlign = 'center';
      g.fillText('!', cx, y - 1 + Math.sin(now / 80) * 2);
    } else {   // a pale dot shows which way a patroller is heading
      g.fillStyle = 'rgba(255,255,255,.55)';
      g.beginPath(); g.arc(cx + DC[e.d] * 22, cy + 4 + DR[e.d] * 22, 3, 0, 7); g.fill();
    }
  }

  function drawHero(g, view, pr, pc) {
    const [x, y] = cell(pr, pc), cx = x + TILE / 2, cy = y + TILE / 2;
    g.globalAlpha = view.dead ? .5 : 1;      // fade the hero when caught

    // Round blue body, a highlight, two eyes looking the way the hero last moved, and a small mouth.
    g.fillStyle = COLOR.hero; g.beginPath(); g.arc(cx, cy, 18, 0, 7); g.fill();
    g.fillStyle = COLOR.heroShine; g.beginPath(); g.arc(cx - 5, cy - 7, 6, 0, 7); g.fill();
    g.fillStyle = COLOR.eye; g.beginPath(); g.arc(cx - 6, cy - 2, 5, 0, 7); g.arc(cx + 6, cy - 2, 5, 0, 7); g.fill();
    g.fillStyle = COLOR.pupil;
    const lx = DC[view.facing] * 2, ly = DR[view.facing] * 2;
    g.beginPath(); g.arc(cx - 6 + lx, cy - 2 + ly, 2.6, 0, 7); g.arc(cx + 6 + lx, cy - 2 + ly, 2.6, 0, 7); g.fill();
    g.fillRect(cx - 4, cy + 7, 8, 2);
    g.globalAlpha = 1;
  }

  /** Floating heart / water ring that fades out where something just happened. */
  function drawEffects(g, view, now) {
    view.effects.forEach(f => {
      // p runs from 0 (just happened) to 1 (finished); the effect rises and fades as p grows.
      const p = (now - f.t0) / EFFECT_MS; if (p < 0 || p > 1) return;
      const [x, y] = cell(f.at[0], f.at[1]);
      g.globalAlpha = 1 - p;
      if (f.kind === 'heart') drawHeart(g, x + TILE / 2, y + TILE / 2 - p * 24, 20 * (1 + p));
      else {
        g.strokeStyle = '#bfe3ff'; g.lineWidth = 3;
        g.beginPath(); g.arc(x + TILE / 2, y + TILE / 2, 9 + p * 22, 0, 7); g.stroke();
      }
      g.globalAlpha = 1;
    });
  }

  function drawBanner(g, W, H, banner) {
    g.fillStyle = 'rgba(20,18,31,.6)'; g.fillRect(0, 0, W, H);     // dim the whole room, then write the message on top

    g.fillStyle = '#fff'; g.textAlign = 'center';
    g.font = 'bold 30px system-ui'; g.fillText(banner.title, W / 2, H / 2 - 6);
    g.font = '16px system-ui'; g.fillText(banner.subtitle, W / 2, H / 2 + 22);
  }

  /** Paint the whole room. `now` is a high-resolution timestamp in ms. */
  function drawRoom(g, view, now) {
    const { L } = view.room, W = L.w * TILE, H = L.h * TILE;
    g.clearRect(0, 0, W, H);
    // Back to front: floor/walls/water, the door, hearts, blocks, ghosts, the hero, then effects and overlays.
    for (let r = 0; r < L.h; r++) for (let c = 0; c < L.w; c++) drawTerrain(g, view, r, c, now);
    drawDoor(g, view);

    // Hearts bob up and down a little (a sine wave of the time), offset by position so they do not move in lock-step.
    view.state.hearts.forEach(k => {
      const [r, c] = k.split(',').map(Number), [x, y] = cell(r, c);
      drawHeart(g, x + TILE / 2, y + TILE / 2 + Math.sin(now / 300 + r + c) * 2, 26);
    });

    // 1 at the start of a move animation, falling to 0: how far things still have to slide.
    const a = view.anim && now - view.anim.t0 < SLIDE_MS ? 1 - (now - view.anim.t0) / SLIDE_MS : 0;

    // Blocks: only the block that was just pushed slides; it starts one cell behind and moves forward as `a` falls to 0.
    view.state.blocks.forEach(k => {
      let [r, c] = k.split(',').map(Number);
      if (a && view.anim.pushed && !view.anim.prevBlocks.has(k)) { r -= DR[view.anim.d] * a; c -= DC[view.anim.d] * a; }
      drawBlock(g, r, c);
    });
    // Ghosts glide from where they were to where they are now.
    view.state.enemies.forEach((e, i) => {
      const before = view.anim && view.anim.prevEnemies[i];
      const r = a && before ? e.r + (before.r - e.r) * a : e.r;
      const c = a && before ? e.c + (before.c - e.c) * a : e.c;
      drawEnemy(g, view, e, r, c, now);
    });

    // The hero slides the same way, except after a wait (the hero did not move then).
    let [pr, pc] = view.state.player;
    if (a && view.anim.prevPlayer && !view.anim.waited) {
      pr += (view.anim.prevPlayer[0] - pr) * a; pc += (view.anim.prevPlayer[1] - pc) * a;
    }
    drawHero(g, view, pr, pc);
    drawEffects(g, view, now);
    // Optional coordinate overlay (see drawAxes), drawn above the pieces but under the banner.
    if (view.axes) drawAxes(g, L, view.hover, view.axes);
    if (view.banner) drawBanner(g, W, H, view.banner);
  }

  /**
   * Optional coordinate overlay, origin (0, 0) at the bottom-left, x to the right, y upward.
   * mode 1: label every CELL by its (x, y); mode 2: label the grid LINES, so a point sits where two lines cross.
   * `hover` = [r, c] highlights one cell.
   */
  function drawAxes(g, L, hover, mode) {
    const W = L.w * TILE, H = L.h * TILE;
    g.save();                                   // so our font / alignment changes do not leak out
    g.strokeStyle = mode === 2 ? 'rgba(255,255,255,.3)' : 'rgba(255,255,255,.12)'; g.lineWidth = 1;
    g.beginPath();
    for (let c = 0; c <= L.w; c++) { g.moveTo(c * TILE + .5, 0); g.lineTo(c * TILE + .5, H); }
    for (let r = 0; r <= L.h; r++) { g.moveTo(0, r * TILE + .5); g.lineTo(W, r * TILE + .5); }
    g.stroke();
    // Highlight the cell under the mouse pointer, if any.
    if (hover) { g.fillStyle = 'rgba(255,225,74,.22)'; g.fillRect(hover[1] * TILE, hover[0] * TILE, TILE, TILE); }
    g.font = 'bold 13px ui-rounded, system-ui, sans-serif'; g.textAlign = 'center'; g.textBaseline = 'middle';
    // A label: a dark rounded-ish backing plate so the yellow number stays readable on any tile.
    const tag = (txt, x, y) => {
      g.fillStyle = 'rgba(20,18,31,.75)'; g.fillRect(x - 9, y - 8, 18, 16);
      g.fillStyle = '#ffe14a'; g.fillText(txt, x, y);
    };
    if (mode === 2) {
      // Line labels: 0..w along the bottom and 0..h up the left, placed ON the lines; small dots mark each crossing.
      for (let c = 0; c <= L.w; c++) tag(String(c), Math.min(W - 9, Math.max(9, c * TILE)), H - 9);
      for (let y = 0; y <= L.h; y++) tag(String(y), 10, Math.min(H - 9, Math.max(8, H - y * TILE)));
      g.fillStyle = '#ffe14a';
      for (let c = 0; c <= L.w; c++) for (let r = 0; r <= L.h; r++) g.fillRect(c * TILE - 1, r * TILE - 1, 3, 3);
    } else {
      // Cell labels: one number per column along the bottom and one per row up the left.
      // Rows are counted from the top of the picture, so y = L.h - 1 - r puts y = 0 at the bottom.
      for (let c = 0; c < L.w; c++) tag(String(c), c * TILE + TILE / 2, H - 9);
      for (let r = 0; r < L.h; r++) tag(String(L.h - 1 - r), 10, r * TILE + TILE / 2);
    }
    g.restore();
  }

  window.Render = { TILE, drawRoom };
})();
