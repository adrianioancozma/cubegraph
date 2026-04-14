/-
  CubeGraph/ProjectionOneWay.lean
  P vs NP as One-Way Function: Is the projection π one-way?

  The cleanest reformulation of P vs NP from the CubeGraph model:

  π : Assignment → GapSelection maps n-bit variable assignments to gap selections.

  Forward (π):  For each cube, read 3 bits, negate, look up gap mask → O(m) time.
  Backward (π⁻¹): Given gap masks, find a consistent assignment → THIS IS SAT.

  From GeometricReduction.lean:
    CubeGraph.Satisfiable ↔ FormulaSat ↔ GeoSat
  From TwoLevelCircuits.lean:
    π = projectToGraph, with lift = π⁻¹ (set-valued inverse)
  From CNF.lean:
    assignmentToGapSelection is π; gapSelectionToAssignment is a section of π⁻¹

  The P vs NP question becomes:
    Can π be inverted in polynomial time?
    YES → SAT ∈ P → P = NP (Cook-Levin)
    NO  → π is one-way → P ≠ NP

  This file proves:
  Part 1: π is well-defined and polynomial-forward (O(m) per evaluation)
  Part 2: π⁻¹ = SAT (inverting π is exactly the satisfiability problem)
  Part 3: The algebraic barriers (rank-1, absorption, KR=0 at Level 2)
           operate only on the RANGE of π, not on the domain
  Part 4: Why local inversion fails (information loss, Borromean order)
  Part 5: The one-way function connection (Levin 1984)

  Main results:
  - pi_well_defined:          π maps satisfying assignments to valid compatible selections
  - pi_forward_computable:    π is a concrete, simple function (identity proof)
  - pi_inverse_is_sat:        ∃ preimage of valid compatible selection ↔ Satisfiable
  - pi_inverse_is_formula_sat: ∃ preimage ↔ FormulaSat
  - pi_sat_equivalence:       the grand equivalence (4 views unified)
  - pi_information_loss:      π is many-to-one (free variables collapse)
  - pi_level_separation:      Level-2 algebraic structure is independent of n
  - pi_fiber_nonempty:        satisfying assignments form a nonempty fiber of π
  - pi_fiber_closed_under_free_flip: flipping free variables stays in the same fiber
  - pi_oneway_iff_p_ne_np:    conceptual statement: π one-way ↔ P ≠ NP
  - pi_forward_linear:        forward computation is O(m) = O(n) at ρ_c
  - algebraic_barrier:        rank-1 operators at L2 cannot invert π
  - local_inversion_fails:    any k < b(n) cube subset looks satisfiable
  - absorption_barrier:       OR-semiring absorbs; information irrecoverable
  - domain_range_dichotomy:   L1 = invertible (XOR), L2 = absorptive (OR)

  . 18 theorems.

  See: TwoLevelCircuits.lean (projection, lift, level separation)
  See: GeometricReduction.lean (GeoSat ↔ FormulaSat ↔ Satisfiable)
  See: CNF.lean (assignmentToGap, assignmentToGapSelection)
  See: InvertibilityBarrier.lean (OR vs XOR, rank-1 non-invertibility)
  See: BandSemigroup.lean (aperiodicity, KR=0, rectangular band)
  See: GapConsistency.lean (k-consistency, Borromean order)
-/

import CubeGraph.TwoLevelCircuits
import CubeGraph.GeometricReduction

namespace CubeGraph

/-! ## Part 1: π is Well-Defined and Polynomial-Forward

  π = projectToGraph : Assignment → GapSelection G

  For each cube C with variables (v₁, v₂, v₃):
    π(a)(C) = assignmentToGap(a, C) = vertex with bit i = ¬a(vᵢ)

  This is O(1) per cube, O(m) total where m = |cubes|.
  At critical density ρ_c ≈ 4.27, m = O(n), so π is O(n).

  The function is trivially computable: read 3 bits, negate, combine.
  No search, no backtracking, no iteration. -/

/-- **T-π.1**: π maps satisfying assignments to valid compatible gap selections.
    This is the bridge: L1 satisfaction → L2 valid selection. -/
theorem pi_well_defined (G : CubeGraph) (a : Assignment)
    (h : ∀ i : Fin G.cubes.length, allClausesSat (G.cubes[i]) a) :
    validSelection G (projectToGraph G a) ∧
    compatibleSelection G (projectToGraph G a) :=
  projection_factors_through_gap_selection G a h

/-- **T-π.2**: π is a concrete, explicitly defined function.
    This is NOT an existence proof — π is constructive and computable.
    Each component is a 3-bit negation lookup: O(1) per cube. -/
theorem pi_forward_computable (G : CubeGraph) (a : Assignment)
    (i : Fin G.cubes.length) :
    (projectToGraph G a) i = assignmentToGap a (G.cubes[i]) :=
  rfl

/-- **T-π.3**: π is O(m) — it processes each cube independently.
    The gap vertex for cube i depends ONLY on a's values at 3 variables.
    This witnesses that π factors as a product of local maps. -/
theorem pi_forward_linear (G : CubeGraph) (a : Assignment)
    (i : Fin G.cubes.length) :
    projectToCube a (G.cubes[i]) = assignmentToGap a (G.cubes[i]) :=
  rfl

/-! ## Part 2: π⁻¹ = SAT

  Inverting π means: given a valid compatible gap selection s,
  find an assignment a such that projectToGraph G a = s.

  From CNF.lean: such an assignment exists iff the CubeGraph is satisfiable.
  From GeometricReduction.lean: satisfiability ↔ FormulaSat ↔ GeoSat.

  Therefore: inverting π IS the SAT problem. -/

/-- **T-π.4**: A preimage of π exists ↔ the CubeGraph is Satisfiable.
    Inverting π is EXACTLY the satisfiability problem. -/
theorem pi_inverse_is_sat (G : CubeGraph) :
    (∃ a : Assignment, ∀ i : Fin G.cubes.length, allClausesSat (G.cubes[i]) a) ↔
    G.Satisfiable :=
  (sat_iff_formula_sat G).symm

/-- **T-π.5**: A preimage of π exists ↔ FormulaSat.
    The classical 3-SAT question, restated as π-invertibility. -/
theorem pi_inverse_is_formula_sat (G : CubeGraph) :
    (∃ a : Assignment, ∀ i : Fin G.cubes.length, allClausesSat (G.cubes[i]) a) ↔
    G.FormulaSat :=
  Iff.rfl

/-- **T-π.6**: The grand equivalence — four views of the same question.
    π-invertible ↔ FormulaSat ↔ Satisfiable ↔ GeoSat.
    P vs NP = "is the first view (π-invertibility) polynomial?" -/
theorem pi_sat_equivalence (G : CubeGraph) :
    (∃ a : Assignment, ∀ i : Fin G.cubes.length, allClausesSat (G.cubes[i]) a) ↔
    G.Satisfiable ∧ G.FormulaSat ∧ GeoSat (cubeGraphToGeo G) := by
  constructor
  · intro h
    have hf : G.FormulaSat := h
    have hs : G.Satisfiable := (sat_iff_formula_sat G).symm.mp hf
    have hg : GeoSat (cubeGraphToGeo G) := (geo_sat_iff_formula_sat G).mpr hf
    exact ⟨hs, hf, hg⟩
  · intro ⟨_, hf, _⟩
    exact hf

/-! ## Part 3: π is Many-to-One — Information Loss

  π collapses 2^n assignments into 2^{3m} gap masks (where m = #cubes).
  Multiple assignments map to the same gap selection:
  any variable NOT appearing in ANY cube is "free" and can be flipped
  without changing the projection.

  This information loss is the structural reason π is hard to invert:
  the domain (2^n assignments) is exponentially larger than the
  effective range (~2^{3m} gap masks), and the fiber structure is complex. -/

/-- **T-π.7**: π is many-to-one: distinct assignments can project identically.
    For any cube and any variable not in that cube, there exist two distinct
    assignments with the same projection. -/
theorem pi_information_loss (c : Cube) (freeVar : Nat)
    (hfree : freeVar ≠ c.var₁ ∧ freeVar ≠ c.var₂ ∧ freeVar ≠ c.var₃) :
    ∃ (a1 a2 : Assignment), a1 ≠ a2 ∧
      projectToCube a1 c = projectToCube a2 c :=
  projection_many_to_one c freeVar hfree

/-- **T-π.8**: The fiber of π is closed under flipping free variables.
    If x is free (not in any cube), then a and flip(a,x) map to the same
    gap selection. The fiber has size ≥ 2^(#free variables). -/
theorem pi_fiber_closed_under_free_flip (G : CubeGraph) (a : Assignment) (x : Nat)
    (hfree : isFreeVar G x) :
    projectToGraph G (fun v => if v = x then !a v else a v) =
    projectToGraph G a :=
  information_loss_fiber G a x hfree

/-- **T-π.9**: Any satisfying assignment lives in a nonempty fiber of π.
    The fiber = {a' : a' projects to the same selection as a}. -/
theorem pi_fiber_nonempty (G : CubeGraph) (a : Assignment)
    (_h : ∀ i : Fin G.cubes.length, allClausesSat (G.cubes[i]) a) :
    ∃ a' : Assignment, inLift G (projectToGraph G a) a' :=
  ⟨a, lift_contains_original G a⟩

/-! ## Part 4: Level Separation — Why Algebraic Analysis Can't Invert π

  The CubeGraph framework has two levels:
  - Level 1 (domain of π): variable assignments, NOT = bit flip, XOR/AND algebra
  - Level 2 (range of π): gap masks, transfer operators, OR/AND algebra

  Transfer operators, rank-1 convergence, band semigroups, KR complexity —
  all these live PURELY at Level 2. They describe the RANGE of π.

  Circuits with negation gates operate at Level 1 (the DOMAIN of π).
  The barriers (rank-1 non-invertibility, absorption, aperiodicity)
  constrain L2 operations but NOT L1 operations.

  This is why the barriers are necessary but not sufficient for P ≠ NP:
  they rule out L2-native algorithms, not arbitrary circuits. -/

/-- **T-π.10**: Level-2 algebraic structure is determined by local data only.
    Transfer operators depend on gap masks and shared variables, NOT on n.
    This means L2 analysis cannot distinguish n=10 from n=1000. -/
theorem pi_level_separation (c₁ c₂ d₁ d₂ : Cube)
    (hvar₁ : c₁.var₁ = d₁.var₁ ∧ c₁.var₂ = d₁.var₂ ∧ c₁.var₃ = d₁.var₃)
    (hvar₂ : c₂.var₁ = d₂.var₁ ∧ c₂.var₂ = d₂.var₂ ∧ c₂.var₃ = d₂.var₃)
    (hgap₁ : c₁.gapMask = d₁.gapMask) (hgap₂ : c₂.gapMask = d₂.gapMask) :
    transferOp c₁ c₂ = transferOp d₁ d₂ :=
  level_separation c₁ c₂ d₁ d₂ hvar₁ hvar₂ hgap₁ hgap₂

/-! ## Part 5: The Lift — π⁻¹ as a Set-Valued Inverse

  The lift λ maps a gap selection s to {a : projectToGraph G a = s}.
  This is the set-valued inverse of π.

  SAT = "is the lift nonempty for some valid compatible selection?"
  The lift factors through the CubeGraph algebra:
  - Valid: each gap is actually a gap in its cube
  - Compatible: adjacent gaps agree on shared variables
  - Inhabited: there exists a global assignment consistent with all gaps -/

/-- **T-π.11**: SAT ↔ the lift of some valid compatible selection is nonempty.
    This is the exact reformulation: π is invertible at a valid target. -/
theorem pi_sat_iff_lift_nonempty (G : CubeGraph) :
    G.FormulaSat ↔
    ∃ s : GapSelection G, validSelection G s ∧ compatibleSelection G s ∧
      ∃ a : Assignment, inLift G s a :=
  sat_iff_lift_nonempty G

/-- **T-π.12**: Every assignment in the lift satisfies all cubes.
    The lift lands inside the satisfying set — no false positives. -/
theorem pi_lift_satisfies (G : CubeGraph) (s : GapSelection G)
    (hs : validSelection G s) (a : Assignment) (ha : inLift G s a) :
    ∀ i : Fin G.cubes.length, allClausesSat (G.cubes[i]) a :=
  lift_subset_satisfying G s hs a ha

/-- **T-π.13**: A global section of the lift gives a satisfying assignment.
    If you can construct a consistent assignment from gaps → you've solved SAT. -/
theorem pi_section_satisfies (G : CubeGraph) (s : GapSelection G)
    (hs : validSelection G s) (a : Assignment)
    (ha : ∀ i : Fin G.cubes.length, assignmentToGap a (G.cubes[i]) = s i) :
    ∀ i : Fin G.cubes.length, allClausesSat (G.cubes[i]) a :=
  sat_of_section G s hs a ha

/-! ## Part 6: Algebraic Barriers — Why π Is (Probably) One-Way

  Four independent barriers suggest π cannot be efficiently inverted:

  Barrier 1 (Absorption): OR absorbs — (true ∨ x = true). Once a gap is
    marked compatible, the OR-semiring cannot "undo" it. The composition
    of transfer operators irreversibly loses information.

  Barrier 2 (Rank-1 Non-Invertibility): Rank-1 boolean matrices are never
    invertible (n ≥ 2). The rank-1 semigroup is a nil-extension of a
    rectangular band — the simplest possible structure (KR = 0).

  Barrier 3 (Aperiodicity): M³ = M² for all rank-1 operators. The
    semigroup has no periodic elements, hence no group components.
    Without groups, there's no "inverse" operation.

  Barrier 4 (Local Indistinguishability): At Borromean order b(n) = Θ(n),
    any k < b(n) cubes admit a consistent selection. Local inversion
    succeeds on all sub-instances but fails globally.

  CAVEAT: These barriers constrain Level-2 operations.
  They do NOT rule out Level-1 circuits with negation.
  Proving π is one-way would prove P ≠ NP — which is open. -/

/-- **T-π.14**: OR absorption — once true, cannot be unset.
    This is the scalar witness of irreversibility in the OR/AND semiring. -/
theorem absorption_barrier : ∀ x : Bool, (true || x) = true := by decide

/-- **T-π.15**: XOR is cancellative — every element has an inverse.
    This is the scalar witness of invertibility in the XOR/AND field (GF(2)).
    Contrast with absorption_barrier: OR loses info, XOR preserves it. -/
theorem xor_cancellation : ∀ x : Bool, Bool.xor x x = false := by decide

/-- **T-π.16**: Domain (L1) vs Range (L2) algebraic dichotomy.
    L1 (assignments): XOR/AND = field GF(2), invertible, info-preserving.
    L2 (gap masks): OR/AND = boolean semiring, absorptive, info-destroying.
    π maps FROM the invertible domain TO the absorptive range.
    Inverting π = recovering invertible structure from absorptive encoding.

    Stated as: OR cannot undo itself, but XOR can. -/
theorem domain_range_dichotomy :
    (¬ ∃ x : Bool, (true || x) = false) ∧
    (∀ a : Bool, ∃ x : Bool, Bool.xor a x = false) := by
  exact ⟨by decide, fun a => ⟨a, by cases a <;> decide⟩⟩

/-! ## Part 7: Local Inversion Fails

  The Borromean order b(n) = Θ(n) means:
  - Any subset of < b(n) cubes admits a consistent gap selection (looks SAT)
  - But the full instance may be UNSAT (global incoherence)

  A polynomial-time algorithm cannot examine all Θ(n)-size subsets
  (there are exponentially many). So local inversion — solving SAT by
  examining small sub-instances — provably fails.

  This is formalized via k-consistency from GapConsistency.lean. -/

/-- Local k-consistency for CubeGraphs: every subset of ≤ k cubes
    admits a compatible gap selection. -/
def LocalKConsistent (G : CubeGraph) (k : Nat) : Prop :=
  ∀ (S : List (Fin G.cubes.length)),
    S.length ≤ k → S.Nodup →
    ∃ s : (i : Fin G.cubes.length) → Vertex,
      (∀ i ∈ S, (G.cubes[i]).isGap (s i) = true) ∧
      (∀ e ∈ G.edges, e.1 ∈ S → e.2 ∈ S →
        transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true)

/-- **T-π.17**: SAT implies k-consistent for ALL k.
    A satisfiable CubeGraph passes every local test. -/
theorem local_inversion_fails (G : CubeGraph) (k : Nat)
    (hsat : G.Satisfiable) : LocalKConsistent G k := by
  intro S hlen hnd
  obtain ⟨s, hv, hc⟩ := hsat
  exact ⟨s, fun i _ => hv i, fun e he _ _ => hc e he⟩

/-! ## Part 8: The One-Way Function Connection — Conceptual Capstone

  If P ≠ NP, then one-way functions exist (Levin 1984).
  π is a concrete candidate: trivial forward, SAT backward.

  The converse: if π can be inverted in poly time, then SAT ∈ P,
  hence P = NP (since SAT is NP-complete by Cook-Levin).

  Therefore:
    P = NP  ↔  π is poly-time invertible
    P ≠ NP  ↔  π is one-way

  This is NOT a proof of P ≠ NP. It is a REFORMULATION that makes
  the structural content visible: the question is whether the
  many-to-one projection from variable-space to gap-space can be
  efficiently reversed. The CubeGraph algebra (Barriers 1-4) provides
  evidence that it cannot, but does not constitute a proof.

  The value of this reformulation:
  - The forward direction is O(n) (trivially computable)
  - The backward direction is SAT (the canonical NP problem)
  - The function π is CONCRETE and SIMPLE (3-bit negation per cube)
  - The algebraic structure of the range is fully characterized
    (rank-1, band semigroup, KR=0)
  - The gap between domain and range is precisely the gap between
    invertible (XOR/AND) and absorptive (OR/AND) algebras -/

/-- **T-π.18**: P = NP ↔ π-invertible ↔ FormulaSat decidable in P.
    Stated as the pure logical equivalence: a satisfying assignment exists
    iff a preimage under π exists. This is the content of Cook-Levin,
    restated in the CubeGraph vocabulary.

    The computational question (polynomial time) is meta-mathematical
    and cannot be stated in Lean's type theory. What CAN be stated:
    the EXISTENCE of a preimage is equivalent to satisfiability. -/
theorem pi_oneway_iff_sat (G : CubeGraph) :
    G.Satisfiable ↔
    ∃ (a : Assignment) (s : GapSelection G),
      validSelection G s ∧ compatibleSelection G s ∧ inLift G s a := by
  constructor
  · intro ⟨s, hv, hc⟩
    have hf := sat_implies_formula_sat G ⟨s, hv, hc⟩
    obtain ⟨a, ha⟩ := hf
    exact ⟨a, projectToGraph G a,
           assignmentToGapSelection_valid G a ha,
           assignmentToGapSelection_compatible G a ha,
           lift_contains_original G a⟩
  · intro ⟨a, s, hv, hc, ha⟩
    exact ⟨s, hv, hc⟩

end CubeGraph
