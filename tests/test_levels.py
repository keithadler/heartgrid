"""Checks on the shipped curriculum (levels.json, web/levels.js and the generated Lean files).

Run with:  python3 -m unittest discover tests
"""
import json, os, re, sys, unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'tools'))
from rules import parse, run, won   # noqa: E402

def read(*parts):
    with open(os.path.join(ROOT, *parts)) as f:
        return f.read()


LEVELS = json.loads(read('levels.json'))


def distance_bound(rows):
    """Shortest tour start -> every heart (best order) -> door, in whole steps along rows and columns."""
    from itertools import permutations
    pos = {ch: [] for ch in 'PHE'}
    for r, row in enumerate(rows):
        for c, ch in enumerate(row):
            if ch in pos: pos[ch].append((r, c))
    d = lambda a, b: abs(a[0] - b[0]) + abs(a[1] - b[1])
    best = 10 ** 9
    for order in permutations(pos['H']):
        stops = [pos['P'][0], *order, pos['E'][0]]
        best = min(best, sum(d(a, b) for a, b in zip(stops, stops[1:])))
    return best


class CurriculumTests(unittest.TestCase):
    def test_distance_bound_never_exceeds_the_minimum(self):
        for lv in LEVELS:
            self.assertLessEqual(distance_bound(lv['rows']), lv['opt'], f"room {lv['n']}")

    def test_twelve_rooms(self):
        self.assertEqual([lv['n'] for lv in LEVELS], list(range(1, 13)))

    def test_every_solution_wins(self):
        for lv in LEVELS:
            L = parse(lv['rows'])
            self.assertTrue(won(L, run(L, lv['sol'])), f"room {lv['n']}")
            self.assertEqual(len(lv['sol']), lv['opt'], f"room {lv['n']}")

    def test_no_prefix_of_a_solution_wins_early(self):
        for lv in LEVELS:
            L = parse(lv['rows'])
            self.assertFalse(won(L, run(L, lv['sol'][:-1])), f"room {lv['n']}")

    def test_difficulty_strictly_increases(self):
        opts = [lv['opt'] for lv in LEVELS]
        self.assertEqual(opts, sorted(set(opts)), opts)

    def test_rooms_are_well_formed(self):
        for lv in LEVELS:
            text = ''.join(lv['rows'])
            for ch, n in (('P', 1), ('E', 1), ('N', 1)):
                self.assertEqual(text.count(ch), n, f"room {lv['n']} has {text.count(ch)} of {ch}")
            self.assertGreater(text.count('H'), 0)
            self.assertEqual(len({len(r) for r in lv['rows']}), 1, 'rectangular')

    def test_rooms_chain_door_to_door(self):
        opposite = {'U': 'D', 'D': 'U', 'L': 'R', 'R': 'L'}
        for a, b in zip(LEVELS, LEVELS[1:]):
            self.assertEqual(b['enter'], opposite[a['exit']], f"rooms {a['n']}->{b['n']}")

    def test_game_data_matches_source_of_truth(self):
        js = read('web', 'levels.js')
        game = json.loads(re.match(r'window\.LEVELS = (.*);\s*$', js, re.S).group(1))
        for lv, g in zip(LEVELS, game):
            for key in ('n', 'name', 'rows', 'sol', 'opt', 'enter', 'exit', 'x', 'y'):
                self.assertEqual(lv[key], g[key], f"room {lv['n']} {key}")

    def test_lean_files_exist_and_mention_the_right_optimum(self):
        for lv in LEVELS:
            src = read('HeartGrid', 'Rooms', f"R{lv['n']:02d}.lean")
            self.assertIn(f"theorem L{lv['n']}_min : MinMoves L{lv['n']} {lv['opt']}", src)
            self.assertIn(f"acts \"{lv['sol']}\"", src)
            self.assertNotIn('sorry', src)


if __name__ == '__main__':
    unittest.main()
