/**
 * minimap.js - the little world map: one box per room, laid out by which wall each exit is on.
 * Rooms carry world coordinates (x, y) in levels.js; a yellow dot marks the door to the next room.
 */
(function () {
  // PAD: empty border round the map.  MAX_CELL_W/H: biggest a room box may get, so a small map is not stretched.
  const PAD = 8, MAX_CELL_W = 54, MAX_CELL_H = 36;
  // current = the room you are in; solved = you cleared it; visited = earlier than the current room; locked = not reached yet.
  const COLOR = { current: '#ff5d8f', solved: '#2f9d6e', visited: '#4a4377', locked: '#2a2646', door: '#ffe9a8' };

  /** Pixel box of every room on a canvas of the given size. */
  function layout(levels, width, height) {
    // Every room has a grid position (x, y) in the world; rooms are drawn as boxes on that grid.
    const xs = levels.map(l => l.x), ys = levels.map(l => l.y);
    const minX = Math.min(...xs), minY = Math.min(...ys);
    // Size the grid of boxes so it fits inside the canvas, then centre it.
    const cols = Math.max(...xs) - minX + 1, rows = Math.max(...ys) - minY + 1;
    const w = Math.min(MAX_CELL_W, (width - 2 * PAD) / cols), h = Math.min(MAX_CELL_H, (height - 2 * PAD) / rows);
    const ox = (width - w * cols) / 2, oy = (height - h * rows) / 2;
    // One pixel rectangle per room, in the same order as `levels`.
    return levels.map(l => ({ x: ox + (l.x - minX) * w, y: oy + (l.y - minY) * h, w, h }));
  }

  /** Draw the map. `solved(n)` says whether room number n has been cleared. */
  function draw(canvas, levels, current, solved) {
    const g = canvas.getContext('2d'), boxes = layout(levels, canvas.width, canvas.height);
    g.clearRect(0, 0, canvas.width, canvas.height);
    levels.forEach((lv, i) => {
      const b = boxes[i];                       // this room's rectangle
      // Colour by state: pink = here, green = cleared, mid purple = already passed, dark = still ahead.
      g.fillStyle = i === current ? COLOR.current : solved(lv.n) ? COLOR.solved : i <= current ? COLOR.visited : COLOR.locked;
      g.fillRect(b.x + 2, b.y + 2, b.w - 4, b.h - 4);
      // A small yellow dot on the edge of the box shows which side the door to the NEXT room is on.
      if (i < levels.length - 1) {
        const next = levels[i + 1];                // direction to the next room = difference of the two grid positions
        g.fillStyle = COLOR.door;
        g.fillRect(b.x + b.w / 2 + (next.x - lv.x) * (b.w / 2 - 2) - 2, b.y + b.h / 2 + (next.y - lv.y) * (b.h / 2 - 2) - 2, 4, 4);
      }
      // The room number, centred in its box.
      g.fillStyle = '#fff'; g.font = '10px system-ui'; g.textAlign = 'center';
      g.fillText(lv.n, b.x + b.w / 2, b.y + b.h / 2 + 3);
    });
  }

  /** Index of the room under a mouse event, or -1. */
  function hit(canvas, levels, event) {
    const r = canvas.getBoundingClientRect();     // the canvas may be shown at a different size than its pixel size
    // Convert the mouse position from screen pixels to canvas pixels, then find the box that contains it.
    const x = (event.clientX - r.left) * canvas.width / r.width, y = (event.clientY - r.top) * canvas.height / r.height;
    return layout(levels, canvas.width, canvas.height).findIndex(b => x >= b.x && x < b.x + b.w && y >= b.y && y < b.y + b.h);
  }

  window.Minimap = { draw, hit };
})();
