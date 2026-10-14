"""The Python reference rules and the browser (JavaScript) engine must agree on every action.

Random action sequences are played in both and the end states compared.  (Lean's model is held to the
same reference by replaying every solution; see HeartGrid/Rooms.)  Needs `node`.

Run with:  python3 -m unittest discover tests
"""
import json, os, random, shutil, subprocess, sys, unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'tools'))
from rules import parse, step   # noqa: E402

def read(*parts):
    with open(os.path.join(ROOT, *parts)) as f:
        return f.read()


LEVELS = json.loads(read('levels.json'))


def summary(s):
    p, bl, he, wa, en, dead = s
    return [list(p), dead, len(he), len(bl), len(wa), sorted(f'{r},{c}' for r, c in bl),
            [[e[0], e[1], e[2], e[3]] for e in en]]


@unittest.skipUnless(shutil.which('node'), 'node not installed')
class CrossEngineTests(unittest.TestCase):
    def test_random_walks_agree(self):
        rng = random.Random(2026)
        cases, expected = [], []
        for lv in LEVELS:
            L = parse(lv['rows'])
            for _ in range(40):
                # bias walks towards the real solution so they get deep into the room
                actions = list(lv['sol'][:rng.randint(0, len(lv['sol']))]) + rng.choices('UDLRS', k=rng.randint(0, 60))
                s = L['start']
                for a in actions: s = step(L, s, a)
                cases.append({'rows': lv['rows'], 'actions': ''.join(actions)})
                expected.append(summary(s))
        out = subprocess.run(['node', os.path.join(ROOT, 'tests', 'replay.js')], input=json.dumps(cases),
                             capture_output=True, text=True, check=True).stdout
        got = json.loads(out)
        self.assertEqual(len(got), len(expected))
        for i, (g, e) in enumerate(zip(got, expected)):
            self.assertEqual(g, e, f"case {i}: room rows[0]={cases[i]['rows'][0]} actions={cases[i]['actions']}")


if __name__ == '__main__':
    unittest.main()
