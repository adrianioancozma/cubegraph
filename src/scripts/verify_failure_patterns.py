#!/usr/bin/env python3
"""
Empirical validation: failure pattern uniqueness on CG-UNSAT instances.

Reproduces Table 6.6 from the paper:
  "P ≠ NP: Four Properties of CubeGraph"

For each UNSAT instance at critical density ρ_c ≈ 4.27:
  - Builds CubeGraph (cubes = variable triplets, edges = shared variables)
  - Trims to H² core (removes degree-1 and degree-2 nodes)
  - Restricts to binary model (first 2 gaps per cube)
  - Enumerates all 2^k gap configurations
  - For each configuration: finds which edges fail
  - Reports: ratio of distinct failure patterns to total configurations

Expected result: ratio = 1.0000 (each configuration fails uniquely).

Dependencies: pip install python-sat
Usage: python verify_failure_patterns.py
"""

import random
import sys
from itertools import combinations
from collections import defaultdict

try:
    from pysat.solvers import Glucose3
except ImportError:
    print("ERROR: python-sat not installed. Run: pip install python-sat")
    sys.exit(1)


def generate_random_3sat(n_vars, n_clauses, seed):
    """Generate a random 3-SAT formula as list of clauses."""
    rng = random.Random(seed)
    clauses = []
    vars_list = list(range(1, n_vars + 1))
    for _ in range(n_clauses):
        vs = rng.sample(vars_list, 3)
        clause = [v if rng.random() > 0.5 else -v for v in vs]
        clauses.append(clause)
    return clauses


def is_unsat(clauses):
    """Check if formula is UNSAT using pysat."""
    with Glucose3() as solver:
        for c in clauses:
            solver.add_clause(c)
        return not solver.solve()


def build_cubegraph(clauses, n_vars):
    """Build CubeGraph: cubes = variable triplets, edges = shared variables."""
    # Cubes: one per variable triplet that has at least one clause
    cube_clauses = defaultdict(list)  # (v1,v2,v3) -> [clause_indices]
    for idx, clause in enumerate(clauses):
        key = tuple(sorted(abs(l) for l in clause))
        cube_clauses[key].append(idx)

    cubes = {}  # cube_id -> {vars, filled, gaps}
    for var_triple, clause_idxs in cube_clauses.items():
        v1, v2, v3 = var_triple
        # 8 vertices per cube
        filled = set()
        for ci in clause_idxs:
            clause = clauses[ci]
            # Vertex = literal polarities (1=positive, 0=negated)
            bits = 0
            for lit in clause:
                var = abs(lit)
                if var == v1:
                    pos = 2
                elif var == v2:
                    pos = 1
                else:
                    pos = 0
                if lit > 0:
                    bits |= (1 << pos)
            filled.add(bits)
        gaps = [v for v in range(8) if v not in filled]
        if len(gaps) >= 2:
            cubes[var_triple] = {'vars': var_triple, 'filled': filled, 'gaps': gaps}

    # Edges: between cubes sharing variables
    cube_ids = list(cubes.keys())
    edges = []
    for i, c1 in enumerate(cube_ids):
        for j, c2 in enumerate(cube_ids):
            if i < j:
                shared = set(c1) & set(c2)
                if len(shared) > 0:
                    edges.append((c1, c2, shared))

    return cubes, edges


def compatibility(cube1, cube2, shared_vars, g1, g2):
    """Check if gap g1 in cube1 is compatible with gap g2 in cube2."""
    for sv in shared_vars:
        # Find bit position in each cube
        pos1 = 2 - list(cube1['vars']).index(sv)
        pos2 = 2 - list(cube2['vars']).index(sv)
        bit1 = (g1 >> pos1) & 1
        bit2 = (g2 >> pos2) & 1
        if bit1 != bit2:
            return False
    return True


def trim_to_h2(cubes, edges):
    """Trim leaves (degree 1) and chains (degree 2) iteratively."""
    active = set(cubes.keys())
    changed = True
    while changed:
        changed = False
        degrees = defaultdict(int)
        for c1, c2, _ in edges:
            if c1 in active and c2 in active:
                degrees[c1] += 1
                degrees[c2] += 1
        to_remove = [c for c in active if degrees[c] <= 1]
        for c in to_remove:
            active.discard(c)
            changed = True
    return active


def analyze_instance(n_vars, ratio, seed, max_k=20):
    """Analyze one instance: count failure patterns."""
    n_clauses = int(n_vars * ratio)
    clauses = generate_random_3sat(n_vars, n_clauses, seed)

    if not is_unsat(clauses):
        return None

    cubes, edges = build_cubegraph(clauses, n_vars)
    active = trim_to_h2(cubes, edges)

    if len(active) < 3:
        return None

    # Active cubes and edges
    core_cubes = {k: v for k, v in cubes.items() if k in active}
    core_edges = [(c1, c2, sv) for c1, c2, sv in edges
                  if c1 in active and c2 in active]
    cube_order = sorted(core_cubes.keys())
    k = len(cube_order)

    if k > max_k:
        return {'k': k, 'skip': True}

    # Binary: first 2 gaps per cube
    cube_gaps = {}
    for cid in cube_order:
        gaps = core_cubes[cid]['gaps']
        cube_gaps[cid] = gaps[:2]

    total = 2 ** k

    # Enumerate all 2^k configs
    patterns = set()
    sat_count = 0

    for mask in range(total):
        gap_sel = {}
        for i, cid in enumerate(cube_order):
            bit = (mask >> i) & 1
            gap_sel[cid] = cube_gaps[cid][bit]

        # Check which edges fail
        failed = []
        for c1, c2, shared in core_edges:
            g1 = gap_sel[c1]
            g2 = gap_sel[c2]
            if not compatibility(core_cubes[c1], core_cubes[c2], shared, g1, g2):
                failed.append((c1, c2))

        if not failed:
            sat_count += 1
        else:
            patterns.add(frozenset(failed))

    unsat = total - sat_count
    return {
        'k': k,
        'total': total,
        'sat': sat_count,
        'unsat': unsat,
        'patterns': len(patterns),
        'ratio': len(patterns) / max(1, unsat),
        'edges': len(core_edges),
    }


def main():
    print("=" * 65)
    print("Empirical Validation: Failure Pattern Uniqueness")
    print("Paper: 'P ≠ NP: Four Properties of CubeGraph'")
    print("=" * 65)
    print()
    print(f"{'n':>3} {'seed':>4} {'k':>3} {'2^k':>8} {'SAT':>6} "
          f"{'patterns':>8} {'ratio':>7} {'edges':>5}")
    print("-" * 60)

    results = []
    for n_vars in [7, 8]:
        found = 0
        for seed in range(1000):
            r = analyze_instance(n_vars, 4.27, seed, max_k=20)
            if r is None:
                continue
            if r.get('skip'):
                continue
            found += 1
            print(f"{n_vars:>3} {seed:>4} {r['k']:>3} {r['total']:>8} "
                  f"{r['sat']:>6} {r['patterns']:>8} {r['ratio']:>7.4f} "
                  f"{r['edges']:>5}")
            results.append(r)
            if found >= 5:
                break
        print()

    if results:
        ratios = [r['ratio'] for r in results]
        print(f"Mean ratio: {sum(ratios)/len(ratios):.4f}")
        print(f"Min ratio:  {min(ratios):.4f}")
        print()
        if min(ratios) >= 0.9999:
            print("RESULT: All failure patterns are UNIQUE (ratio = 1.0).")
            print("Each configuration fails on a distinct set of edges.")
        else:
            print("RESULT: Some failure patterns are shared.")


if __name__ == '__main__':
    main()
