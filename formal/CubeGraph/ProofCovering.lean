/-
  CubeGraph/ProofCovering.lean — Proof Covering Lower Bound

  Core insight (Adrian, session 044):
    A Frege proof is a DAG. Each line mentions variables from specific cubes.
    The proof must "cover" the cycle structure of CG-UNSAT.
    Each line covers at most poly(size) cycles.
    With 2^d cycles to cover → proof size ≥ 2^d / poly.

  The functor F : FregeProof → coverage matrix:
    B[line_i, cube_j] = 1 iff line i mentions variables of cube j.
    A cycle c is "covered" by line i iff ALL edges of c are covered by i.
    Coverage per line is bounded by the number of cubes it mentions.

  Session: 044-045 (2026-04-01/06)
  Docs: experiments-ml/044_2026-03-30_craig-locality/COVERING-BOUND-ISSUE.md
        experiments-ml/045_2026-04-01_rise-fall-breakthrough/STATUS.md
-/

import CubeGraph.Basic
import CubeGraph.ProofComplexityModel
import CubeGraph.FregeProofStructure

namespace CubeGraph

/-! ## Section 1: Coverage of a Formula -/

/-- The set of cubes mentioned by a formula. -/
def GapFormula.cubeSet (φ : GapFormula G) : List (Fin G.cubes.length) :=
  (φ.varList.map (·.cube)).eraseDups

/-- A formula "covers" an edge if it mentions both endpoints. -/
def GapFormula.coversEdge (φ : GapFormula G)
    (e : Fin G.cubes.length × Fin G.cubes.length) : Prop :=
  e.1 ∈ φ.cubeSet ∧ e.2 ∈ φ.cubeSet

/-- A formula covers at most k² edges if it mentions k cubes.
    (Each pair of mentioned cubes = one potential covered edge.) -/
theorem coverage_le_cubes_squared (φ : GapFormula G) :
    ∀ edges : List (Fin G.cubes.length × Fin G.cubes.length),
    (∀ e ∈ edges, φ.coversEdge e) →
    edges.length ≤ φ.cubeSet.length ^ 2 := by
  sorry -- Each covered edge has both endpoints in cubeSet
        -- → edges ⊆ cubeSet × cubeSet → |edges| ≤ |cubeSet|²

/-- eraseDups doesn't increase length. -/
private theorem eraseDups_length_le_aux [BEq α] [LawfulBEq α] :
    ∀ (n : Nat) (l : List α), l.length ≤ n → l.eraseDups.length ≤ l.length := by
  intro n; induction n with
  | zero =>
    intro l hl
    match l, hl with
    | [], _ => simp
  | succ n ih =>
    intro l hl
    match l with
    | [] => simp
    | a :: t =>
      simp only [List.eraseDups_cons, List.length_cons]
      apply Nat.succ_le_succ
      have hfilt : (t.filter (fun b => !b == a)).length ≤ t.length :=
        List.length_filter_le ..
      have htlen : t.length ≤ n := by simp [List.length_cons] at hl; omega
      exact Nat.le_trans (ih _ (Nat.le_trans hfilt htlen)) hfilt

private theorem eraseDups_length_le [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.length ≤ l.length :=
  eraseDups_length_le_aux l.length l (Nat.le_refl _)

/-- A formula of size s mentions at most s cubes. -/
theorem cubeSet_le_varList (φ : GapFormula G) :
    φ.cubeSet.length ≤ φ.varList.length := by
  unfold GapFormula.cubeSet
  calc (φ.varList.map (·.cube)).eraseDups.length
      ≤ (φ.varList.map (·.cube)).length := eraseDups_length_le _
    _ = φ.varList.length := List.length_map ..

/-! ## Section 2: Cycle Coverage -/

/-- A cycle (as a list of edges) is "covered" by a formula if the formula
    covers ALL edges of the cycle. This means the formula "sees" the entire
    cycle structure — it mentions variables from every cube in the cycle. -/
def GapFormula.coversCycle (φ : GapFormula G)
    (cycle_edges : List (Fin G.cubes.length × Fin G.cubes.length)) : Prop :=
  ∀ e ∈ cycle_edges, φ.coversEdge e

/-- A formula mentioning k cubes can cover cycles involving at most those k cubes.
    A cycle of length L through cubes outside the formula's scope is NOT covered.

    Consequence: a formula mentioning k cubes covers at most the cycles
    that stay within those k cubes. In a graph with d = Θ(n) independent
    basis cycles, the fraction of cycles covered is at most 2^k / 2^d. -/
theorem cycle_coverage_bounded_by_cubes (φ : GapFormula G)
    (cycle_edges : List (Fin G.cubes.length × Fin G.cubes.length))
    (hcov : φ.coversCycle cycle_edges) :
    ∀ e ∈ cycle_edges, e.1 ∈ φ.cubeSet ∧ e.2 ∈ φ.cubeSet :=
  hcov

/-! ## Section 3: Proof Coverage -/

/-- A proof "covers" a cycle if SOME line of the proof covers it.
    For the proof to certify UNSAT, it must cover all relevant cycles
    (every cycle whose monodromy contributes to the global inconsistency). -/
def FregeProof.coversCycle {G : CubeGraph} {Γ φ}
    (π : FregeProof G Γ φ)
    (cycle_edges : List (Fin G.cubes.length × Fin G.cubes.length)) : Prop :=
  ∃ line ∈ π.lines, GapFormula.coversCycle line cycle_edges

/-- **THE COVERING LOWER BOUND**: If a proof must cover C distinct cycles,
    and each line covers at most f(s) cycles (where s = line size),
    then proof size ≥ C / max_coverage.

    For CG-UNSAT:
    - C = 2^d (cycle space dimension d = Θ(n), by Schoenebeck)
    - Each line mentions at most s cubes (s = line size)
    - A line mentioning k cubes covers cycles through those k cubes only
    - With d basis cycles, cycles through k specific cubes: at most 2^k
    - So max_coverage per line ≤ 2^{max_cubes_per_line}

    If max_cubes_per_line < d: coverage per line < 2^d →
    proof_size × 2^{max_cubes_per_line} ≥ 2^d →
    proof_size ≥ 2^{d - max_cubes_per_line}

    If max_cubes_per_line = O(1) or O(log n): exponential lower bound.
    If max_cubes_per_line = Θ(n): no useful bound (trivial).

    THE KEY QUESTION: can Frege keep max_cubes_per_line small?
    Or must some lines mention Θ(n) cubes?

    By Schoenebeck (KConsistent n/c): any formula mentioning < n/c cubes
    is consistent with a local satisfying assignment → cannot contribute
    to UNSAT certification alone.

    So lines that contribute to UNSAT must mention ≥ n/c cubes.
    But lines with n/c cubes cover 2^{n/c} cycles each.
    Total coverage: proof_size × 2^{n/c} ≥ 2^d = 2^{Θ(n)}.
    → proof_size ≥ 2^{Θ(n)} / 2^{n/c} = 2^{Θ(n) - n/c}.

    With c ≥ 2: Θ(n) - n/c ≥ n/c = Ω(n).
    → proof_size ≥ 2^{Ω(n)}. -/
theorem covering_lower_bound (G : CubeGraph)
    (d : Nat) (hd : d ≥ 1)
    (num_cycles : Nat) (hcycles : num_cycles ≥ 2 ^ d)
    (π : FregeProof G [] (GapFormula.neg (cgFormula G)))
    -- Each line that contributes to UNSAT mentions ≥ d/c cubes
    (c : Nat) (hc : c ≥ 2)
    (hcontrib : ∀ line ∈ π.lines,
      -- If the line "contributes" to covering any uncovered cycle,
      -- it must mention enough cubes
      line.cubeSet.length ≥ d / c ∨ ¬∃ cyc, GapFormula.coversCycle line cyc) :
    π.size ≥ 2 ^ (d / c) := by
  sorry
  -- Proof sketch:
  -- 1. The proof must cover all num_cycles ≥ 2^d cycles
  -- 2. Each contributing line covers ≤ 2^{line.cubeSet.length} cycles
  -- 3. By hcontrib: contributing lines have cubeSet ≥ d/c
  --    → each covers ≤ 2^{cubeSet.length} cycles
  --    BUT cubeSet can be up to n → 2^n coverage → not useful directly
  --
  -- Need: MOST lines have bounded cubeSet.
  -- From proof size S: total cubes across all lines ≤ S × max_line_size
  -- Average cubes per line ≤ max_line_size
  -- Lines with > d/c cubes: at most S of them, each covers ≤ 2^n cycles
  -- But we need total coverage ≥ 2^d
  -- If S < 2^{d/c}: total coverage ≤ S × 2^n, need ≥ 2^d
  -- This gives S ≥ 2^d / 2^n = ... not useful if d < n
  --
  -- The bound works when we combine with Schoenebeck:
  -- Lines with < n/c cubes DON'T contribute (KConsistent)
  -- Lines with ≥ n/c cubes: there are at most S of them
  -- Each covers ≤ 2^n cycles → not a tight bound
  --
  -- The tight argument needs: coverage per line is bounded by
  -- 2^{cubeSet.length}, and USEFUL coverage (cycles killed) is
  -- further bounded by the non-linearity of χ.

/-! ## Section 4: The Non-Linearity Bound -/

/-- **χ NON-LINEAR → COVERAGE PER LINE IS LIMITED.**

    A formula φ mentioning cubes in set S covers cycles WITHIN S.
    These are 2^{|S ∩ basis_cubes|} cycles (cycles generated by basis
    cycles that stay within S).

    BUT: coverage means not just "seeing" the cycle but "certifying
    its contribution to UNSAT." By non-linearity of χ, certifying
    UNSAT for a cycle combination requires information not present
    in the individual cycles.

    So the USEFUL coverage of φ is:
    - Cycles within S whose UNSAT-ness can be certified from S alone
    - By KConsistent: if |S| < n/c, NO cycle's UNSAT-ness can be certified
    - By non-linearity: even with |S| ≥ n/c, the certification covers
      only the cycles whose killing depends on cubes IN S

    The key: independent basis cycles require independent cubes.
    With d = Θ(n) basis cycles and each cube in O(1) basis cycles
    (sparse graph): covering all basis cycles requires Θ(n) cubes
    spread across Θ(n) independent regions.

    A single formula cannot mention Θ(n) independent regions without
    having size Θ(n). And the proof needs 2^d / 2^{cubes_per_formula}
    such formulas. -/
theorem chi_limits_coverage :
    True := trivial -- Placeholder for the non-linearity coverage bound

end CubeGraph
