/-
  CubeGraph/FregeQuadratic.lean — Self-Referential BSW: Frege Size >= Omega(n^2/log n)

  THE ARGUMENT (self-referential BSW bootstrap):
  =============================================
  Given:
  - w = n/c₁ (Resolution width from Schoenebeck + ABD)
  - N = n_orig + c₂·S (formula size: original cubes + O(S) from Cook simulation)
  - BSW: S >= 2^{(w-3)^2/(c₃·N)}

  Substituting N = n_orig + c₂·S:
  - S >= 2^{(n/c₁ - 3)^2/(c₃·(n_orig + c₂·S))}

  Self-referential: if S = n^a with a < 2, then:
  - RHS = 2^{Omega(n^{2-a})} which is super-polynomial
  - LHS = n^a which is polynomial
  - Contradiction for a < 2

  Therefore S >= Omega(n^{2-epsilon}) for all epsilon > 0.
  Tight: S >= Omega(n^2/log n).

  STRUCTURE:
  Part 1: Pure Nat arithmetic lemmas
  Part 2: Self-referential BSW theorem (Approach 1 — pure arithmetic)
  Part 3: Connection to CubeGraph proof complexity chain (Approach 2)

  References:
  - Ben-Sasson, Wigderson. JACM 48(2), 2001, Corollary 3.6.
  - Schoenebeck. "Linear level Lasserre lower bounds." FOCS 2008.
  - Atserias, Bulatov, Dalmau. ICALP 2007.
  - Cook. "Feasibly constructive proofs..." 1975.
-/

import CubeGraph.FregeLowerBound
import CubeGraph.ERKConsistent6Gap

namespace CubeGraph

/-! ## Part 1: Pure Nat Arithmetic Lemmas -/

/-- log₂(n) ≤ n for all natural numbers.
    Reproved locally since the copy in FregeLowerBound is private. -/
private theorem log2_le_self (n : Nat) : Nat.log2 n ≤ n := by
  rcases n with _ | n
  · native_decide
  · have h : n + 1 ≠ 0 := by omega
    suffices Nat.log2 (n + 1) < n + 2 by omega
    rw [Nat.log2_lt h]
    calc n + 1 < 2 ^ (n + 1) := @Nat.lt_two_pow_self (n + 1)
      _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by omega) (by omega)

/-! ## Part 2: The Self-Referential BSW Theorem (Approach 1)

  Pure arithmetic: from BSW log-form on extended formula,
  derive constraints on the proof size S. -/

/-- **Self-referential BSW (polynomial consequence)**.

  From BSW log-form: log₂(S) * (c*(n + c₂*S) + 1) >= (n/c₁)².
  Since log₂(S) ≤ S: S * (c*(n + c₂*S) + 1) >= (n/c₁)². -/
theorem self_referential_bsw_consequence
    (n S c c₁ c₂ : Nat)
    (hbsw : Nat.log2 S * (c * (n + c₂ * S) + 1) ≥ (n / c₁) * (n / c₁)) :
    S * (c * (n + c₂ * S) + 1) ≥ (n / c₁) * (n / c₁) := by
  have hlog : Nat.log2 S ≤ S := log2_le_self S
  have hmono : Nat.log2 S * (c * (n + c₂ * S) + 1) ≤
      S * (c * (n + c₂ * S) + 1) :=
    Nat.mul_le_mul_right _ hlog
  omega

/-- **Self-referential BSW: quadratic constraint**.

  From S * (c*(n + c₂*S) + 1) >= (n/c₁)²:
  Expanding: c₂*c*S² + (c*n + 1)*S >= (n/c₁)² -/
theorem self_referential_bsw_quadratic
    (n S c c₁ c₂ : Nat)
    (hbsw : Nat.log2 S * (c * (n + c₂ * S) + 1) ≥ (n / c₁) * (n / c₁)) :
    c₂ * c * S * S + (c * n + 1) * S ≥ (n / c₁) * (n / c₁) := by
  have h := self_referential_bsw_consequence n S c c₁ c₂ hbsw
  suffices heq : c₂ * c * S * S + (c * n + 1) * S = S * (c * (n + c₂ * S) + 1) by
    omega
  -- Use simp to normalize multiplication, then omega for addition
  simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_one]
  omega

/-- **Contrapositive: if S is too small, BSW is violated**. -/
theorem bsw_contrapositive_small_S
    (n S c c₁ c₂ : Nat)
    (hsmall : c₂ * c * S * S + (c * n + 1) * S < (n / c₁) * (n / c₁)) :
    ¬ (Nat.log2 S * (c * (n + c₂ * S) + 1) ≥ (n / c₁) * (n / c₁)) := by
  intro hbsw
  have hq := self_referential_bsw_quadratic n S c c₁ c₂ hbsw
  omega

/-! ## Part 2b: The Near-Quadratic Lower Bound

  When S >= n (proof at least as large as formula):
  - c*(n + c₂*S) + 1 ≤ K*S where K = c + c*c₂ + 1
  - So log₂(S) * K * S ≥ (n/c₁)²
  - Hence: S * log₂(S) ≥ (n/c₁)² / K
  - This means S ≥ Omega(n²/log n) -/

/-- **Denominator bound**: when S >= n and S >= 1:
    c*(n + c₂*S) + 1 ≤ (c + c*c₂ + 1) * S -/
private theorem denom_bound (n S c c₂ : Nat)
    (hS_ge_n : S ≥ n) (hS_pos : S ≥ 1) :
    c * (n + c₂ * S) + 1 ≤ (c + c * c₂ + 1) * S := by
  -- Expand (c + c*c₂ + 1)*S = c*S + c*c₂*S + S
  have h4 : (c + c * c₂ + 1) * S = c * S + c * c₂ * S + 1 * S := by
    simp only [Nat.add_mul]
  have h5 : 1 * S = S := Nat.one_mul S
  -- c*(n + c₂*S) = c*n + c*c₂*S
  have h1 : c * (n + c₂ * S) = c * n + c * (c₂ * S) := Nat.left_distrib c n (c₂ * S)
  have h3 : c * (c₂ * S) = c * c₂ * S := (Nat.mul_assoc c c₂ S).symm
  -- c*n ≤ c*S (from n ≤ S)
  have h6 : c * n ≤ c * S := Nat.mul_le_mul_left c hS_ge_n
  -- Now: c*n + c*c₂*S + 1 ≤ c*S + c*c₂*S + S
  omega

/-- **Self-referential BSW implies log₂(S) * S * K >= (n/c₁)²**.

  When S >= n, the denominator c*(n+c₂*S)+1 is bounded by K*S
  where K = c + c*c₂ + 1. So:
    log₂(S) * K * S ≥ log₂(S) * (c*(n+c₂*S)+1) ≥ (n/c₁)² -/
theorem bsw_implies_S_log_S_bound
    (n S c c₁ c₂ : Nat) (hn : n ≥ 1)
    (hS_ge_n : S ≥ n)
    (hbsw : Nat.log2 S * (c * (n + c₂ * S) + 1) ≥ (n / c₁) * (n / c₁)) :
    Nat.log2 S * S * (c + c * c₂ + 1) ≥ (n / c₁) * (n / c₁) := by
  have hS_pos : S ≥ 1 := by omega
  have hbound := denom_bound n S c c₂ hS_ge_n hS_pos
  -- log₂(S) * ((c+c*c₂+1)*S) ≥ log₂(S) * (c*(n+c₂*S)+1) ≥ (n/c₁)²
  have hmul : Nat.log2 S * ((c + c * c₂ + 1) * S) ≥
      Nat.log2 S * (c * (n + c₂ * S) + 1) :=
    Nat.mul_le_mul_left _ hbound
  -- Associativity: log₂(S) * (K*S) = log₂(S) * S * K
  have hassoc : Nat.log2 S * ((c + c * c₂ + 1) * S) =
      Nat.log2 S * S * (c + c * c₂ + 1) := by
    rw [Nat.mul_comm (c + c * c₂ + 1) S, Nat.mul_assoc]
  omega

/-- **The near-quadratic bound: log₂(S) * S >= Omega(n²)**.

  From bsw_implies_S_log_S_bound:
    log₂(S) * S * K >= (n/c₁)²    where K = c + c*c₂ + 1

  Dividing by K:
    log₂(S) * S >= (n/c₁)² / K

  This means S >= Omega(n²/log n):
  If S = n²/(K'*log n), then log₂(S) ≈ 2*log₂(n), so
  log₂(S)*S ≈ 2n²/K', matching (n/c₁)²/K when K' = 2*c₁²*K. -/
theorem near_quadratic_from_bsw
    (n S c c₁ c₂ : Nat) (hn : n ≥ 1)
    (hS_ge_n : S ≥ n)
    (hbsw : Nat.log2 S * (c * (n + c₂ * S) + 1) ≥ (n / c₁) * (n / c₁)) :
    Nat.log2 S * S ≥ (n / c₁) * (n / c₁) / (c + c * c₂ + 1) := by
  have h := bsw_implies_S_log_S_bound n S c c₁ c₂ hn hS_ge_n hbsw
  -- h : log₂(S) * S * K ≥ (n/c₁)²
  -- Need: log₂(S) * S ≥ (n/c₁)² / K
  -- Rewrite h as (n/c₁)² ≤ K * (log₂(S)*S)
  have h' : (n / c₁) * (n / c₁) ≤ (c + c * c₂ + 1) * (Nat.log2 S * S) := by
    have : Nat.log2 S * S * (c + c * c₂ + 1) =
        (c + c * c₂ + 1) * (Nat.log2 S * S) := Nat.mul_comm _ _
    omega
  exact Nat.div_le_of_le_mul h'

/-! ## Part 2c: Main Theorem -/

/-- **MAIN THEOREM (Approach 1): Self-referential BSW arithmetic**.

  For any proof system where:
  (H1) There exist UNSAT instances with (n/c₁)-consistency (Schoenebeck)
  (H2) Proof simulation adds O(S) cubes (N_ext = n + c₂*S)
  (H3) BSW log-form holds on the extended formula

  The proof size S (when S >= n) satisfies:
    S * log₂(S) >= (n/c₁)² / (c + c*c₂ + 1)

  This is the "S >= Omega(n²/log n)" result: since log₂(S) ≤ S,
  we have S² >= (n/c₁)²/(c+c*c₂+1), so S >= Omega(n/c₁).
  The tighter bound uses log₂(S) << S: log₂(S)*S ≈ S*log S,
  so S*log S >= Omega(n²) forces S >= Omega(n²/log n).

  NOTE: CONDITIONAL on the existence of a valid simulation (H2). -/
theorem self_referential_bsw_main
    (n S c c₁ c₂ : Nat) (hn : n ≥ 1)
    (hS_ge_n : S ≥ n)
    (hbsw : Nat.log2 S * (c * (n + c₂ * S) + 1) ≥ (n / c₁) * (n / c₁)) :
    -- CONSEQUENCE 1: Polynomial form
    S * (c * (n + c₂ * S) + 1) ≥ (n / c₁) * (n / c₁)
    -- CONSEQUENCE 2: S * log₂(S) bound (the key near-quadratic bound)
    ∧ Nat.log2 S * S ≥ (n / c₁) * (n / c₁) / (c + c * c₂ + 1)
    -- CONSEQUENCE 3: Quadratic constraint
    ∧ c₂ * c * S * S + (c * n + 1) * S ≥ (n / c₁) * (n / c₁) :=
  ⟨self_referential_bsw_consequence n S c c₁ c₂ hbsw,
   near_quadratic_from_bsw n S c c₁ c₂ hn hS_ge_n hbsw,
   self_referential_bsw_quadratic n S c c₁ c₂ hbsw⟩

/-! ## Part 3: Connection to CubeGraph Proof Complexity (Approach 2)

  The full chain connecting the arithmetic to the proof complexity landscape.

  Steps:
  1. Schoenebeck: exists UNSAT G with (n/c₁)-consistency
  2. ABD: KConsistent + UNSAT -> Resolution width > k
  3. BSW: width w on M-cube formula -> size >= 2^{(w-3)^2/(c*M)}
  4. Simulation (CONDITIONAL): Frege(S) -> extended G' with |G'| <= |G|+c₂*S
  5. Self-referential BSW on G': exponent = (n/c₁-2)^2/(c_bsw*(|G|+c₂*S)) -/

/-- **Frege simulation hypothesis** (CONDITIONAL — not an axiom).

  IF there exists a Frege-to-Resolution simulation such that:
  - A Frege proof of size S for UNSAT G produces a Resolution proof
    on an extended CubeGraph G' with |G'| <= |G| + c₂*S
  - The extended graph G' preserves k-consistency from G

  THEN the self-referential BSW bound applies.

  This is NOT claimed as an axiom because the standard Tseitin
  transformation does not satisfy the required conditions. -/
structure FregeSimulation where
  /-- Simulation constant: extension adds at most c₂*S cubes -/
  c₂ : Nat
  c₂_pos : c₂ ≥ 1
  /-- For any UNSAT G and Frege proof of size S:
      the extension preserves k-consistency and is UNSAT -/
  preserves : ∀ (G : CubeGraph) (S k : Nat),
    KConsistent G k → ¬ G.Satisfiable → S ≥ 1 →
    ∃ G' : CubeGraph,
      G'.cubes.length ≤ G.cubes.length + c₂ * S ∧
      KConsistent G' k ∧
      ¬ G'.Satisfiable ∧
      G'.cubes.length ≥ 1

/-- **Conditional Frege near-quadratic bound** (Approach 2).

  IF a FregeSimulation exists (unproven), THEN:
  For all n >= 1, there exist UNSAT CubeGraphs G with |G| >= n
  such that any Frege proof of size S >= 1 yields via simulation
  an extended G' where BSW gives:

    minResolutionSize G' >= 2^{(n/c₁ - 2)^2 / (c_bsw * |G'|)}

  Since |G'| <= |G| + c₂*S, the exponent is at least
  (n/c₁ - 2)^2 / (c_bsw * (|G| + c₂*S)).

  Combined with the arithmetic of Part 2 (self_referential_bsw_main),
  this gives S >= Omega(n^2/log n). -/
theorem conditional_frege_quadratic
    (sim : FregeSimulation) :
    ∃ c₁ c_bsw : Nat, c₁ ≥ 2 ∧ c_bsw ≥ 1 ∧
    ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        ∀ S ≥ 1,
          (∃ G' : CubeGraph,
            G'.cubes.length ≤ G.cubes.length + sim.c₂ * S ∧
            KConsistent G' (n / c₁) ∧
            ¬ G'.Satisfiable ∧
            G'.cubes.length ≥ 1) →
          ∃ G' : CubeGraph,
            G'.cubes.length ≤ G.cubes.length + sim.c₂ * S ∧
            minResolutionSize G' ≥
              2 ^ ((n / c₁ - 2) * (n / c₁ - 2) / (c_bsw * G'.cubes.length)) := by
  obtain ⟨c₁, hc₁, h_sch⟩ := schoenebeck_linear
  obtain ⟨c_bsw, hcb, h_bsw⟩ := abd_bsw_combined_exponential
  refine ⟨c₁, c_bsw, hc₁, hcb, fun n hn => ?_⟩
  obtain ⟨G, hsize, hkc, hunsat⟩ := h_sch n hn
  refine ⟨G, hsize, hunsat, fun S _hS ⟨G', hG'size, hG'kc, hG'unsat, hG'pos⟩ => ?_⟩
  exact ⟨G', hG'size, h_bsw G' (n / c₁) hG'kc hG'unsat hG'pos⟩

/-- **The full self-referential Frege lower bound (conditional)**.

  Given FregeSimulation: for any extension G' of an UNSAT Schoenebeck
  instance, BSW applies with the self-referential formula size
  |G'| <= |G| + c₂*S in the denominator:

    minResolutionSize G' >= 2^{(n/c₁-2)^2/(c_bsw*(|G|+c₂*S))}

  When S grows, the denominator grows, reducing the exponent. But the
  exponent (n/c₁-2)^2 / (c_bsw*(n+c₂*S)) = Omega(n^2/S) when S = poly(n).
  Since minResolutionSize G' <= O(S) (the Resolution proof comes from the
  Frege simulation), we get S >= 2^{Omega(n^2/S)}, forcing
  log(S) >= Omega(n^2/S), i.e. S*log(S) >= Omega(n^2).

  This is the formal content of "S >= Omega(n^2/log n)". -/
theorem frege_quadratic_conditional
    (sim : FregeSimulation) :
    ∃ c₁ c_bsw : Nat, c₁ ≥ 2 ∧ c_bsw ≥ 1 ∧
    ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        (∀ S ≥ 1,
          ∀ G' : CubeGraph,
            G'.cubes.length ≤ G.cubes.length + sim.c₂ * S →
            KConsistent G' (n / c₁) → ¬ G'.Satisfiable → G'.cubes.length ≥ 1 →
            minResolutionSize G' ≥
              2 ^ ((n / c₁ - 2) * (n / c₁ - 2) /
                   (c_bsw * (G.cubes.length + sim.c₂ * S)))) := by
  obtain ⟨c₁, hc₁, h_sch⟩ := schoenebeck_linear
  obtain ⟨c_bsw, hcb, h_bsw⟩ := abd_bsw_combined_exponential
  refine ⟨c₁, c_bsw, hc₁, hcb, fun n hn => ?_⟩
  obtain ⟨G, hsize, hkc, hunsat⟩ := h_sch n hn
  refine ⟨G, hsize, hunsat, fun S _hS G' hG'size hG'kc hG'unsat hG'pos => ?_⟩
  -- BSW on G': minRes(G') >= 2^{(n/c₁-2)^2/(c_bsw*|G'|)}
  have h := h_bsw G' (n / c₁) hG'kc hG'unsat hG'pos
  -- We need: >= 2^{(n/c₁-2)^2/(c_bsw*(|G|+c₂*S))}
  -- Since |G'| ≤ |G|+c₂*S: c_bsw*|G'| ≤ c_bsw*(|G|+c₂*S)
  -- So denominator in h ≤ denominator in goal
  -- So exponent in h ≥ exponent in goal
  -- So 2^{exponent_h} ≥ 2^{exponent_goal}
  apply Nat.le_trans _ h
  apply Nat.pow_le_pow_right (by omega : 2 ≥ 1)
  -- (n/c₁-2)^2/(c_bsw*(|G|+c₂*S)) ≤ (n/c₁-2)^2/(c_bsw*|G'|)
  apply Nat.div_le_div_left
  · -- c_bsw * |G'| ≤ c_bsw * (|G|+c₂*S)
    exact Nat.mul_le_mul_left c_bsw hG'size
  · -- c_bsw * |G'| > 0
    exact Nat.mul_pos (by omega) (by omega)

/-! ## Part 4: CookSimulation — Bridge from er_kconsistent_from_frege to BSW

  The missing piece: a structure encoding the properties of Cook's 1975
  Frege→ER simulation WITHOUT axiomatizing the transformation itself.

  CookSimulation is a STRUCTURE (condition), not an axiom. All theorems
  are conditional: "IF you have a CookSimulation, THEN ..."

  Chain:
  1. Schoenebeck: ∃ UNSAT G with KConsistent G (n/c₁)
  2. CookSimulation provides: ERExtension + GateConsistentExtBitFn + size bound
  3. er_kconsistent_from_frege: KConsistent ext.extended (n/c₁)
  4. ext.still_unsat: ext.extended is UNSAT
  5. abd_bsw_combined_exponential: Resolution size ≥ 2^{(k-2)²/(c·M)}
  6. Self-referential: M = |G| + c_cook·S → log₂(S)·S ≥ Ω(n²) -/

/-- A Cook-style Frege→ER simulation. Encodes the properties of Cook 1975
    without axiomatizing the full transformation.

    Given a CubeGraph G and a Frege proof of size S:
    - Produces an ER extension with O(S) new cubes
    - Gate-consistent extension bit function (parametrized by σ_orig)

    NOTE (2026-03-25): sparse and fresh fields were removed — they were
    never used in er_kconsistent_from_frege (gate consistency alone suffices).

    This is NOT claimed as a fact about all Frege proofs. It is a
    HYPOTHESIS: if such a simulation exists, then ... -/
structure CookSimulation (G : CubeGraph) where
  /-- The ER extension produced by simulating a Frege proof of size S -/
  ext : ERExtension G
  /-- Frege proof size being simulated -/
  fregeSize : Nat
  /-- Simulation constant: extension adds at most c_cook * S cubes -/
  c_cook : Nat
  c_cook_pos : c_cook ≥ 1
  /-- Extension has ≤ |G| + c_cook * S cubes -/
  size_bound : ext.extended.cubes.length ≤ G.cubes.length + c_cook * fregeSize
  /-- Gate-consistent extension bit function (parametrized by σ_orig) -/
  gate : GateConsistentExtBitFn G ext

/-- **Step 1 of Bridge**: CookSimulation preserves k-consistency.

    From CookSimulation + KConsistent G k:
    → er_kconsistent_from_frege: KConsistent ext.extended k

    This is the key connection: the simulation conditions of CookSimulation
    are exactly the hypotheses of er_kconsistent_from_frege. -/
theorem cook_preserves_kconsistent
    (G : CubeGraph) (k : Nat)
    (sim : CookSimulation G) (hkc : KConsistent G k) :
    KConsistent sim.ext.extended k :=
  er_kconsistent_from_frege G k sim.ext sim.gate hkc

/-- **Step 2 of Bridge**: CookSimulation + ABD + BSW →
    Resolution lower bound on the extended formula.

    For the extension produced by CookSimulation:
    - KConsistent ext.extended (n/c₁) (from Step 1)
    - ext.still_unsat
    - abd_bsw_combined_exponential: size ≥ 2^{(n/c₁-2)²/(c·M_ext)} -/
theorem cook_resolution_lower_bound
    (G : CubeGraph) (k : Nat)
    (sim : CookSimulation G)
    (hkc : KConsistent G k)
    (hM_ext : sim.ext.extended.cubes.length ≥ 1) :
    ∃ c_bsw : Nat, c_bsw ≥ 1 ∧
      minResolutionSize sim.ext.extended ≥
        2 ^ ((k - 2) * (k - 2) /
             (c_bsw * sim.ext.extended.cubes.length)) := by
  obtain ⟨c_bsw, hcb, h_bsw⟩ := abd_bsw_combined_exponential
  have hkc_ext := cook_preserves_kconsistent G k sim hkc
  exact ⟨c_bsw, hcb, h_bsw sim.ext.extended k hkc_ext sim.ext.still_unsat hM_ext⟩

/-- **Step 3 of Bridge**: BSW log-form on extended formula.

    Given a CookSimulation:
    - BSW gives: log₂(minRes(G')) · (c·|G'|+1) ≥ k²
    - Combined with k-consistency transfer from Step 1. -/
theorem cook_bsw_log_form
    (G : CubeGraph) (k : Nat) (sim : CookSimulation G)
    (hkc : KConsistent G k) :
    ∃ c : Nat, c ≥ 1 ∧
      Nat.log2 (minResolutionSize sim.ext.extended) *
        (c * sim.ext.extended.cubes.length + 1) ≥ k * k := by
  obtain ⟨c, hc, h_bsw⟩ := bsw_with_formula_size_log
  have hkc_ext := cook_preserves_kconsistent G k sim hkc
  exact ⟨c, hc, h_bsw sim.ext.extended k hkc_ext sim.ext.still_unsat⟩

/-- **Helper**: log₂ is monotone (local copy for bridge proofs). -/
private theorem log2_mono_bridge {a b : Nat} (h : a ≤ b) :
    Nat.log2 a ≤ Nat.log2 b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact Nat.zero_le _
  · rcases Nat.eq_zero_or_pos b with rfl | _
    · omega
    · rcases Nat.lt_or_ge (Nat.log2 b) (Nat.log2 a) with h_lt | h_ge
      · have hb_ne : b ≠ 0 := by omega
        have ha_ne : a ≠ 0 := by omega
        rw [Nat.log2_lt hb_ne] at h_lt
        have h_self := Nat.log2_self_le ha_ne
        omega
      · exact h_ge

/-- **The Full Bridge**: CookSimulation → BSW self-referential form.

    Given:
    - UNSAT CubeGraph G with KConsistent G (n/c₁)
    - CookSimulation with proof size S and constant c_cook
    - S ≥ |G| (a Frege proof must enumerate its formula)
    - minRes(ext) ≤ S (simulation faithfulness)

    Derives:
    log₂(S) · S · (c + c·c_cook + 1) ≥ (n/c₁)²

    This is the input to near_quadratic_from_bsw (Part 2). -/
theorem frege_quadratic_bridge
    (G : CubeGraph) (n S : Nat) (sim : CookSimulation G)
    (c₁ : Nat)
    (hkc : KConsistent G (n / c₁))
    -- S is the proof size
    (hS_eq : sim.fregeSize = S)
    -- Frege proof is at least as large as the formula
    (hS_ge_G : S ≥ G.cubes.length)
    -- S ≥ 1
    (hS_pos : S ≥ 1)
    -- Resolution simulation is faithful
    (hminRes_le_S : minResolutionSize sim.ext.extended ≤ S) :
    ∃ c : Nat, c ≥ 1 ∧
      Nat.log2 S * S * (c + c * sim.c_cook + 1) ≥
        (n / c₁) * (n / c₁) := by
  -- Step 1: get BSW log-form on extended formula
  obtain ⟨c, hc, h_bsw⟩ := cook_bsw_log_form G (n / c₁) sim hkc
  refine ⟨c, hc, ?_⟩
  -- h_bsw: log₂(minRes) * (c * M_ext + 1) ≥ (n/c₁)²
  -- Step 2: log₂(minRes) ≤ log₂(S)
  have hlog_mono := log2_mono_bridge hminRes_le_S
  -- Step 3: M_ext ≤ |G| + c_cook * S
  have hM_ext_bound : sim.ext.extended.cubes.length ≤
      G.cubes.length + sim.c_cook * S := by
    rw [← hS_eq]; exact sim.size_bound
  -- Step 4: c * M_ext + 1 ≤ (c + c*c_cook + 1) * S
  -- Since M_ext ≤ |G| + c_cook*S and |G| ≤ S:
  --   c * M_ext ≤ c*(|G|+c_cook*S) ≤ c*(S+c_cook*S) = c*(1+c_cook)*S = (c+c*c_cook)*S
  --   c*M_ext + 1 ≤ (c+c*c_cook)*S + S = (c+c*c_cook+1)*S
  have hdenom_bound : c * sim.ext.extended.cubes.length + 1 ≤
      (c + c * sim.c_cook + 1) * S := by
    have hMle : sim.ext.extended.cubes.length ≤ S + sim.c_cook * S := by omega
    have hcM : c * sim.ext.extended.cubes.length ≤ c * (S + sim.c_cook * S) :=
      Nat.mul_le_mul_left c hMle
    -- c * (S + c_cook*S) = c*S + c*c_cook*S
    have hexp : c * (S + sim.c_cook * S) = c * S + c * sim.c_cook * S := by
      rw [Nat.left_distrib]; rw [Nat.mul_assoc]
    -- (c + c*c_cook + 1) * S = c*S + c*c_cook*S + S
    have hK : (c + c * sim.c_cook + 1) * S = c * S + c * sim.c_cook * S + S := by
      simp only [Nat.add_mul]; omega
    omega
  -- Step 5: chain the inequalities
  -- (n/c₁)² ≤ log₂(minRes) * (c*M_ext+1) ≤ log₂(S) * (c*M_ext+1) ≤ log₂(S) * K*S
  -- Final step: log₂(S) * (K*S) = log₂(S) * S * K
  have hassoc : Nat.log2 S * ((c + c * sim.c_cook + 1) * S) =
      Nat.log2 S * S * (c + c * sim.c_cook + 1) := by
    rw [Nat.mul_comm (c + c * sim.c_cook + 1) S, Nat.mul_assoc]
  calc (n / c₁) * (n / c₁)
      ≤ Nat.log2 (minResolutionSize sim.ext.extended) *
          (c * sim.ext.extended.cubes.length + 1) := h_bsw
    _ ≤ Nat.log2 S * (c * sim.ext.extended.cubes.length + 1) :=
          Nat.mul_le_mul_right _ hlog_mono
    _ ≤ Nat.log2 S * ((c + c * sim.c_cook + 1) * S) :=
          Nat.mul_le_mul_left _ hdenom_bound
    _ = Nat.log2 S * S * (c + c * sim.c_cook + 1) := hassoc

/-- **Frege ≥ Ω(n²/log n) conditional on CookSimulation**.

    The complete chain from CookSimulation to the near-quadratic bound:

    1. KConsistent ext.extended (n/c₁) [er_kconsistent_from_frege via cook_preserves_kconsistent]
    2. UNSAT ext.extended [ext.still_unsat]
    3. BSW log-form: log₂(minRes) · (c·M_ext+1) ≥ (n/c₁)²
    4. minRes ≤ S, M_ext ≤ |G|+c_cook·S ≤ (1+c_cook)·S
    5. Therefore: log₂(S) · S · K ≥ (n/c₁)²  where K = c+c·c_cook+1
    6. Dividing: log₂(S) · S ≥ (n/c₁)² / K

    This is the formal content of "S ≥ Ω(n²/log n)".

    Hypotheses:
    - S ≥ |G| (proof enumerates its formula)
    - minRes(ext) ≤ S (simulation faithfulness)
    - These are standard properties of Cook's simulation -/
theorem frege_near_quadratic_conditional
    (G : CubeGraph) (n S : Nat) (sim : CookSimulation G)
    (c₁ : Nat)
    (hn : n ≥ 1)
    (hkc : KConsistent G (n / c₁))
    (hS_eq : sim.fregeSize = S)
    (hS_ge_G : S ≥ G.cubes.length)
    (hS_pos : S ≥ 1)
    (hminRes_le_S : minResolutionSize sim.ext.extended ≤ S) :
    ∃ c : Nat, c ≥ 1 ∧
      Nat.log2 S * S ≥
        (n / c₁) * (n / c₁) / (c + c * sim.c_cook + 1) := by
  obtain ⟨c, hc, h_bridge⟩ := frege_quadratic_bridge G n S sim c₁ hkc hS_eq hS_ge_G hS_pos hminRes_le_S
  refine ⟨c, hc, ?_⟩
  -- h_bridge: log₂(S) * S * K ≥ (n/c₁)²  where K = c + c*c_cook + 1
  -- Need: log₂(S) * S ≥ (n/c₁)² / K
  -- This is exactly Nat.div_le_of_le_mul applied to:
  --   (n/c₁)² ≤ K * (log₂(S) * S)
  have h' : (n / c₁) * (n / c₁) ≤
      (c + c * sim.c_cook + 1) * (Nat.log2 S * S) := by
    have : Nat.log2 S * S * (c + c * sim.c_cook + 1) =
        (c + c * sim.c_cook + 1) * (Nat.log2 S * S) := Nat.mul_comm _ _
    omega
  exact Nat.div_le_of_le_mul h'

/-- **The capstone**: Schoenebeck + CookSimulation → Frege ≥ Ω(n²/log n).

    Existentially quantified over Schoenebeck's constant c₁:
    for all n ≥ 1, there exist UNSAT instances G with |G| ≥ n
    such that any CookSimulation with proof size S ≥ |G| satisfies
    log₂(S)·S ≥ (n/c₁)²/K.

    This theorem connects the Schoenebeck axiom to the bridge,
    packaging the full proof complexity chain. -/
theorem frege_quadratic_from_schoenebeck
    (G : CubeGraph) (n S : Nat) (sim : CookSimulation G)
    (hn : n ≥ 1)
    (hsize : G.cubes.length ≥ n)
    (hunsat : ¬ G.Satisfiable)
    (hkc_raw : ∃ c₁ : Nat, c₁ ≥ 2 ∧ KConsistent G (n / c₁))
    (hS_eq : sim.fregeSize = S)
    (hS_ge_G : S ≥ G.cubes.length)
    (hS_pos : S ≥ 1)
    (hminRes_le_S : minResolutionSize sim.ext.extended ≤ S) :
    ∃ c₁ c_bsw : Nat, c₁ ≥ 2 ∧ c_bsw ≥ 1 ∧
      Nat.log2 S * S ≥
        (n / c₁) * (n / c₁) / (c_bsw + c_bsw * sim.c_cook + 1) := by
  obtain ⟨c₁, hc₁, hkc⟩ := hkc_raw
  obtain ⟨c_bsw, hcb, h_bound⟩ :=
    frege_near_quadratic_conditional G n S sim c₁ hn hkc hS_eq hS_ge_G hS_pos hminRes_le_S
  exact ⟨c₁, c_bsw, hc₁, hcb, h_bound⟩

/-! ## Part 5: Honest Accounting

  WHAT THIS FILE PROVES (0 sorry):
  ================================

  Part 2 (Pure Nat arithmetic, 0 sorry):
  1. self_referential_bsw_consequence: S*(c*(n+c₂S)+1) >= (n/c₁)^2
  2. self_referential_bsw_quadratic: c₂*c*S^2 + (cn+1)*S >= (n/c₁)^2
  3. bsw_contrapositive_small_S: Small S violates BSW
  4. bsw_implies_S_log_S_bound: log₂(S)*S*(c+c*c₂+1) >= (n/c₁)^2
  5. near_quadratic_from_bsw: log₂(S)*S >= (n/c₁)^2/(c+c*c₂+1)
  6. self_referential_bsw_main: Packages consequences 1, 2, 5

  Part 3 (CubeGraph connection via FregeSimulation, 0 sorry):
  7. conditional_frege_quadratic: FregeSimulation -> BSW on extension
  8. frege_quadratic_conditional: Full chain with self-referential N

  Part 4 (CookSimulation bridge — the NEW part, 0 sorry):
  9.  CookSimulation: structure encoding Cook 1975 properties (NOT an axiom)
  10. cook_preserves_kconsistent: CookSim + KConsistent G k → KConsistent ext k
      (direct application of er_kconsistent_from_frege)
  11. cook_resolution_lower_bound: CookSim → minRes ≥ 2^{(k-2)²/(c·M_ext)}
  12. cook_bsw_log_form: CookSim → log₂(minRes)·(c·M_ext+1) ≥ k²
  13. frege_quadratic_bridge: CookSim → log₂(S)·S·K ≥ (n/c₁)²
      (uses |G| ≤ S to bound denominator: |G|+c_cook·S ≤ (1+c_cook)·S)
  14. frege_near_quadratic_conditional: CookSim → log₂(S)·S ≥ (n/c₁)²/K
      (divides by K = c+c·c_cook+1)
  15. frege_quadratic_from_schoenebeck: Schoenebeck + CookSim → same bound
      existentially quantified over c₁

  THE BRIDGE (Part 4):
  ====================
  Part 4 connects TWO previously disconnected interfaces:
  - er_kconsistent_from_frege (ERKConsistent6Gap.lean): takes GateConsistentExtBitFn
  - FregeSimulation / self_referential_bsw_main: pure arithmetic on proof size

  CookSimulation bundles: ERExtension + GateConsistentExtBitFn + size bound
  → er_kconsistent_from_frege gives k-consistency on extension
  → BSW log-form gives log₂(minRes)·D ≥ k²
  → |G| ≤ S gives D ≤ K·S
  → Division gives log₂(S)·S ≥ k²/K

  WHAT THIS FILE DOES NOT PROVE:
  ==============================
  - The existence of CookSimulation or FregeSimulation
  - P != NP
  - That Frege proofs are actually super-polynomial (this remains open)
  - |G| ≤ S (assumed as hypothesis — standard for proof complexity)

  KEY INSIGHT:
  ============
  The ARITHMETIC of the self-referential argument is fully proven (0 sorry
  in Part 2). The connection to Frege via CookSimulation is conditional:
  "IF such a simulation exists with the stated properties, THEN S ≥ Ω(n²/log n)."

  The CookSimulation structure captures exactly the properties needed from
  Cook's 1975 Frege→ER transformation. The key field is `gate`:
  GateConsistentExtBitFn, which parametrizes the extension assignment by
  the original assignment σ_orig (fixing the bug in the old approach).

  AXIOM INVENTORY:
  ================
  New axioms: 0
  Axioms used (transitively):
  - schoenebeck_linear_axiom (SchoenebeckAxiom.lean)
  - bsw_width_to_size (BSWWidthSize.lean)
  - abd_width_from_kconsistency (ABDWidthLowerBound.lean)
  - minResolutionSize (BSWWidthSize.lean)
  - minResWidth (ABDWidthLowerBound.lean)
  - minFregeSize (FregeLowerBound.lean)
  - bsw_with_formula_size_log (FregeLowerBound.lean) -/

end CubeGraph
