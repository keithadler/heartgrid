// Replays action strings through the browser engine and prints a summary of each end state.
// stdin: JSON [{rows, actions}]   stdout: JSON [summary]   (used by test_cross_engine.py)
global.window = {};
require('../web/engine.js');
const { Engine } = global.window;

const summary = (L, s) => [
  s.player, s.dead, s.hearts.size, s.blocks.size, s.water.size,
  [...s.blocks].sort(), s.enemies.map(e => [e.r, e.c, e.d, e.hunter]),
];

let input = '';
process.stdin.on('data', d => input += d).on('end', () => {
  const out = JSON.parse(input).map(({ rows, actions }) => {
    const { L, start } = Engine.parse(rows);
    let s = start;
    for (const a of actions) s = Engine.step(L, s, a).state;
    return summary(L, s);
  });
  console.log(JSON.stringify(out));
});
