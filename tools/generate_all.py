"""Generate candidate rooms for all twelve slots in parallel into tools/candidates/.

Rooms 10-12 share one pool (same sides and parameters); build_levels.py splits it by difficulty.
usage: python3 tools/generate_all.py [seconds_per_job]      (default 420)
"""
import os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, 'candidates')
EXITS = 'RRRDLLLDRRRR'                       # which wall each room's exit is on
OPP = {'U': 'D', 'D': 'U', 'L': 'R', 'R': 'L'}
seconds = sys.argv[1] if len(sys.argv) > 1 else '420'


def job(args):
    slot, seed = args
    enter = 'L' if slot == 0 else OPP[EXITS[slot - 1]]
    path = os.path.join(OUT, f'slot{slot:02d}_seed{seed}.jsonl')
    with open(path, 'w') as out:
        subprocess.run(['timeout', seconds, sys.executable, os.path.join(HERE, 'generate_rooms.py'),
                        str(slot), str(seed), '1000', enter, EXITS[slot]], stdout=out, stderr=subprocess.DEVNULL)
    return path


if __name__ == '__main__':
    os.makedirs(OUT, exist_ok=True)
    jobs = [(slot, seed) for slot in range(12) for seed in ((1, 2) if slot < 3 else (11, 12, 13))]
    with ThreadPoolExecutor(max_workers=os.cpu_count() or 4) as pool:
        for path in pool.map(job, jobs): print('done', os.path.basename(path), flush=True)
