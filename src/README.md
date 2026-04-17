# CubeGraph — Empirical Validation Scripts

Scripts reproducing the empirical results from the paper
"P ≠ NP: Four Properties of CubeGraph."

## Setup

```bash
cd src
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

## Reproduce Table 6.6 (Failure Pattern Uniqueness)

```bash
python scripts/verify_failure_patterns.py
```

Expected output: ratio = 1.0000 on all instances.
Each of the 2^k UNSAT configurations fails on a **unique** set of edges.

Runtime: ~2 minutes (n=7), ~30 seconds per instance.

## What the script does

1. Generates random 3-SAT formulas at critical density ρ_c ≈ 4.27
2. Checks UNSAT (via pysat/Glucose3)
3. Builds CubeGraph (variable triplets → cubes, shared variables → edges)
4. Trims to H² core (removes degree ≤ 2 nodes)
5. Restricts to binary model (first 2 gaps per cube)
6. Enumerates all 2^k gap configurations
7. For each: finds which edges fail (failure pattern)
8. Reports: ratio of distinct patterns to total configurations

## Dependencies

- Python ≥ 3.9
- python-sat (SAT solver, `pip install python-sat`)

No other dependencies. The script is self-contained.
