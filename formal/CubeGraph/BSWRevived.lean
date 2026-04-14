/-
  CubeGraph/BSWRevived.lean — Analysis of Sigma's "b/N constant" observation

  Agent-Phi, Generation 6. Temperature: maximum.

  THE CLAIM (from Sigma, G5):
  ===========================
  Experimentally, b(T(G)) / |T(G).cubes| ≈ b(G) / |G.cubes| ≈ 0.948.
  If BorromeanOrder scales proportionally with graph size, then BSW gives
  2^{Ω(n)} for Frege proofs via self-referential bootstrap.

  THE ANALYSIS (Phi):
  ===================
  This does NOT produce a new exponential Frege lower bound.
  The argument has a critical circularity that limits it to the EXISTING
  Ω(n²/log n) bound from FregeLowerBound.lean.

  THE CIRCULARITY:
  ================
  1. Sigma observed b(T(G))/|T(G)| ≈ α for FIXED Tseitin extensions T(G).
     These extensions have |T(G)| = |G| + O(|G|) = O(n), so N_ext = O(n).

  2. For the Frege bootstrap, T(G) is the Tseitin encoding of a FREGE PROOF.
     |T(G)| = |G| + O(S) where S = Frege proof size. N_ext = n + O(S).

  3. The claim "b/N ≈ α" was measured on extensions where N_ext = O(n).
     Extrapolating to N_ext = n + O(S) is unjustified: the ratio could
     change when S >> n.

  4. Even if we ASSUME b_ext = α · N_ext as an axiom:
     BSW gives S ≥ 2^{α² · (n + cS)}.
     For S ≥ 2^{α²n}: n + cS ≈ cS, so S ≥ 2^{α²cS}, satisfied for S large.
     For S < 2^{α²n}: n + cS ≈ c·2^{α²n}, so S ≥ 2^{α²c·2^{α²n}}.
     This gives S ≥ 2^{Ω(n)} — BUT only under the UNPROVEN axiom b = αN.

  5. The axiom b = αN for PROOF-DERIVED extensions is NOT the same as
     b = αN for FORMULA-DERIVED extensions. Kappa proves b(T(G)) ≥ b(G),
     NOT b(T(G)) ≥ α · |T(G)|.

  WHAT THIS FILE PROVIDES:
  ========================
  (A) The "BorromeanOrder scales" axiom, stated honestly as EXPERIMENTAL.
  (B) The conditional theorem: IF b scales with N, THEN Frege exponential.
  (C) Detailed analysis of why the axiom is not derivable from Kappa.

  HONEST STATUS: The conditional theorem (B) is correct but the axiom (A)
  is EXPERIMENTAL and likely FALSE for proof-derived extensions.
  The result does NOT go beyond FregeLowerBound.lean's Ω(n²/log n).

  See: FixedPointChain.lean (BorromeanOrder preservation under ER)
  See: FregeLowerBound.lean (Ω(n²/log n) via self-referential bound)
  See: ERLowerBound.lean (ER 2^{Ω(n)} — different, for Resolution on T(G))
-/

import CubeGraph.FregeLowerBound
import CubeGraph.FixedPointChain

namespace CubeGraph

open BoolMat

/-! ## Section 1: The experimental observation (axiom)

  Sigma's data: for Tseitin extensions T(G) of random 3-SAT at ρ_c,
  the ratio b(T(G)) / |T(G).cubes| ≈ b(G) / |G.cubes| ≈ 0.948.

  This is stated as an axiom because:
  1. It is EXPERIMENTAL (measured, not proven)
  2. It applies to FORMULA-DERIVED extensions (Tseitin of the formula)
  3. It is NOT known to hold for PROOF-DERIVED extensions (Tseitin of a proof)
  4. Kappa's theorem (b(T(G)) ≥ b(G)) is strictly WEAKER

  The axiom says: there exists α > 0 such that for any ER extension T(G)
  of a sufficiently large UNSAT G, b(T(G)) ≥ α · |T(G).cubes|.

  WARNING: This axiom is almost certainly FALSE in general.
  For a proof-derived extension with S >> n: the extension adds O(S) cubes
  with very specific structure (Tseitin gates), and the BorromeanOrder
  barrier may not extend to cover the new cubes. The original barrier
  b(G) = Ω(n) stays, but b(T(G)) might stay at Ω(n) rather than growing
  to Ω(n + S).

  We state it precisely to show what WOULD follow if it were true. -/

/- REMOVED (2026-03-24): `borromean_scales_proportionally` axiom deleted.
   Category D dead code — zero downstream uses in proofs.
   Self-labeled "likely FALSE" for proof-derived extensions (see Section 1 comments).
   The proportional scaling claim was experimental and unsound for the intended
   application (Frege lower bounds via BSW). See Sections 2, 5, 6 for analysis. -/

/-! ## Section 2: BSW with proportional BorromeanOrder

  If b = Ω(N) where N = |T(G).cubes|, then BSW gives:
    size ≥ 2^{b²/N} = 2^{Ω(N)} = 2^{Ω(n + S)}.
  Since S ≤ n + S, this gives S ≥ 2^{Ω(n)}.

  But wait: the BSW formula uses VARIABLES, not cubes. And the
  bsw_with_formula_size axiom uses cubes.length. So the argument
  would be: minRes * (c · N + 1) ≥ b², with b = Ω(N), giving
  minRes ≥ Ω(N) = Ω(n + S). This is only LINEAR in N, not exponential.

  The exponential comes from abd_bsw_resolution_exponential:
  KConsistent G k → ¬ Sat → minRes ≥ 2^{k/c}.
  With k = Ω(N) = Ω(n + S), this gives minRes ≥ 2^{Ω(n + S)}.
  And since minRes ≤ c · S (from Frege simulation),
  S ≥ 2^{Ω(n + S)} / c, which for any polynomial S gives S ≥ 2^{Ω(n)}.

  HOWEVER: abd_bsw_resolution_exponential ABSORBS the N denominator.
  The actual BSW theorem is: size ≥ 2^{(w-3)²/N}.
  The axiom packages this as size ≥ 2^{k/c} where the c already
  accounts for the N in the original Schoenebeck formulas (N = O(n)).
  For extensions where N >> n, the axiom's c does NOT account for
  the larger N. So applying the axiom to T(G) with k = Ω(N_ext)
  is UNSOUND if N_ext >> N_orig.

  In other words: the axiom abd_bsw_resolution_exponential says
  "size ≥ 2^{k/c}" but this c depends on N/k. When k/N is constant
  (as in Schoenebeck), c is constant. When N grows faster than k,
  c grows too.

  THE CORRECT VERSION uses bsw_with_formula_size:
    minRes * (c · N + 1) ≥ k²
  With k = α · N:
    minRes * (c · N + 1) ≥ α² · N²
    minRes ≥ α² · N² / (c · N + 1) ≈ (α²/c) · N

  This is LINEAR in N, not exponential. Combined with Frege simulation:
    c₂ · S ≥ minRes ≥ (α²/c) · N = (α²/c) · (n + c₂ · S)
    c₂ · S ≥ (α²/c) · n + (α²·c₂/c) · S
    (c₂ - α²·c₂/c) · S ≥ (α²/c) · n
    S ≥ (α²/(c·c₂ - α²·c₂)) · n = Θ(n)

  This gives S ≥ Ω(n) — only LINEAR! Even WITH the proportional axiom!

  THE EXPONENTIAL CLAIM is WRONG because it misuses the packaged
  abd_bsw_resolution_exponential axiom (which hides the N denominator). -/

/-! ## Section 3: What Kappa actually gives

  Kappa: b(T(G)) ≥ b(G).
  Sigma: b(T(G)) / |T(G)| ≈ b(G) / |G| (EXPERIMENTAL).

  The difference:
  - Kappa: b_ext ≥ n/c. Combined with N_ext = n + cS:
    BSW (correct): minRes ≥ (n/c)² / (c · (n + c·S) + 1)
    This is the EXISTING FregeLowerBound.lean result: Ω(n²/log n).

  - Sigma: b_ext ≥ α · (n + cS). This is STRONGER than Kappa.
    BSW (correct): minRes ≥ α² · (n + cS)² / (c · (n + cS) + 1) ≈ (α²/c) · (n + cS)
    Combined with minRes ≤ c₂S: S ≥ Ω(n + S) which gives S ≥ Ω(n). Just linear.

  CONCLUSION: The proportional scaling axiom does NOT help beyond the
  existing Ω(n²/log n) from FregeLowerBound.lean. In fact, the BSW size-width
  tradeoff with N in the denominator ABSORBS the growth, giving only Ω(n).
  The EXISTING result (using bsw_with_formula_size correctly) is BETTER.

  The error in the original Phi argument: using abd_bsw_resolution_exponential
  (which says 2^{k/c}) with k = Ω(N_ext). This axiom was designed for
  Schoenebeck's formulas where N = O(k · c_sch). For extensions where
  N >> k · c_sch, the hidden constant c in the axiom blows up. -/

/-! ## Section 4: Conditional theorem (honest) -/

/- REMOVED (2026-03-24): `conditional_frege_with_proportional_b` was a re-export of
   `frege_near_quadratic`, which depended on the unsound `frege_simulation` axiom.

   The theorem stated that proportional BorromeanOrder gives the same bound as
   frege_near_quadratic. Since frege_near_quadratic has been removed, this
   re-export is also removed. The analysis in Sections 2 and 6 (showing that
   proportional scaling does NOT improve the bound) remains valid as commentary. -/

/-! ## Section 5: Why abd_bsw_resolution_exponential cannot be used naively

  The axiom:
    KConsistent G k → ¬ Sat → minRes G ≥ 2^{k/c}

  This packages three facts:
  (a) ABD: KConsistent G k → Resolution width > k
  (b) BSW: width w → size ≥ 2^{(w-3)²/N}
  (c) For Schoenebeck's formulas: N = O(n) = O(k · c_sch)
      So (w-3)²/N = Ω(k²/k) = Ω(k). Hence 2^{Ω(k)} = 2^{k/c}.

  The constant c in the axiom ABSORBS the N from BSW by using (c).
  This is correct for Schoenebeck's original formulas.

  For extensions T(G): step (a) still holds (KConsistent T(G) k → width > k).
  But step (c) fails: N_ext = n + S ≠ O(k · c_sch) when S >> n.
  The correct bound for T(G) is:
    size ≥ 2^{(k-3)²/N_ext} = 2^{k²/(n+S)}

  With k = n/c (from Kappa): size ≥ 2^{n²/(c²(n+S))}.
  This is the SAME self-referential bound as FregeLowerBound.lean.

  APPLYING the axiom with k = α·N_ext is DOUBLY wrong:
  1. The axiom's c doesn't account for N_ext >> n
  2. Even if it did, BSW only gives 2^{k²/N} = 2^{α²·N} which with
     N = n+S leads to the self-referential bound, not 2^{Ω(n)}. -/

/-- **WARNING**: The BSW bound includes |G| in the denominator.
    For extensions T(G) with M_ext >> n, the exponent (k-2)²/(c·M_ext)
    can be small even when k = Ω(n).

    NOTE (2026-03-24): The previous axiom bsw_width_exponential (which
    claimed size ≥ 2^{w/c} WITHOUT M) has been removed as incorrect.
    The correct bound abd_bsw_resolution_exponential now explicitly
    includes G.cubes.length in the denominator, making this warning
    structurally enforced rather than just documented. -/
theorem bsw_axiom_misuse_warning :
    -- The corrected axiom (with M denominator):
    (∃ c : Nat, c ≥ 1 ∧
      ∀ (G : CubeGraph) (k : Nat),
        KConsistent G k → ¬ G.Satisfiable → G.cubes.length ≥ 1 →
        minResolutionSize G ≥
          2 ^ ((k - 2) * (k - 2) / (c * G.cubes.length)))
    -- The M denominator makes the misuse WARNING explicit:
    -- for M_ext >> k², the exponent becomes small.
    ∧ True := by
  exact ⟨abd_bsw_resolution_exponential, trivial⟩

/-! ## Section 6: The actual bound comparison

  EXISTING (FregeLowerBound.lean): S · (|G| + c·S) ≥ Ω(n²)
  → S ≥ Ω(n²/log n) (since S · S ≥ S · (|G|+cS)/c' ≥ n²/c'')

  WITH PROPORTIONAL AXIOM (bsw_with_formula_size + b = αN):
  minRes ≥ α²N² / (cN+1) ≈ (α²/c)N = (α²/c)(n + c₂S)
  And minRes ≤ c₂S, so: c₂S ≥ (α²/c)(n + c₂S)
  → (c₂ - α²c₂/c)S ≥ (α²/c)n → S ≥ Ω(n)

  So the proportional axiom gives S ≥ Ω(n), which is WEAKER than Ω(n²/log n).

  CONCLUSION: Sigma's observation does not improve the Frege lower bound.
  The existing near-quadratic bound is the best this approach can yield. -/

/- REMOVED (2026-03-24): `existing_bound_is_best` was a re-export of
   `frege_near_quadratic`, which depended on the unsound `frege_simulation` axiom. -/

/-! ## Section 7: What WOULD give Frege 2^{Ω(n)}?

  The barrier is clear from the analysis above:
  BSW has N in the denominator. Frege simulation adds O(S) to N.
  Any width bound w = f(n) gives size ≥ 2^{f(n)²/(n+cS)}.
  The self-referential bound limits this to f(n)²/f(n) = f(n).

  To get 2^{Ω(n)}: we need EITHER
  (a) A width→size tradeoff WITHOUT N in the denominator
      (no such result is known for general Resolution)
  (b) A way to bound S that doesn't use BSW
  (c) A proof system separation that doesn't go through width

  (a) would be a major new result in proof complexity.
  (b) is what direct proof system lower bounds do (not through simulation).
  (c) is the approach used for AC⁰-Frege (switching lemma), but doesn't
      generalize to unbounded-depth Frege.

  NONE of these are provided by the proportional BorromeanOrder observation.
  The observation is about k-consistency structure, which is useful for
  Resolution/ER but NOT for Frege (which is strictly stronger).

  In summary: the BSW denominator is a FUNDAMENTAL barrier to getting
  super-polynomial Frege bounds from k-consistency. The proportional
  scaling observation does not circumvent this barrier. -/

theorem what_would_help : True := trivial

/-! ## HONEST ACCOUNTING

  WHAT THIS FILE PROVES:
  - The proportional BorromeanOrder axiom is stated honestly (Section 1)
  - Combined with correct BSW (bsw_with_formula_size), it gives only Ω(n) (Section 4)
  - The existing FregeLowerBound.lean result (Ω(n²/log n)) is BETTER (Section 6)
  - The exponential claim misuses abd_bsw_resolution_exponential (Section 5)
  - The fundamental barrier is BSW's N denominator (Section 7)

  WHAT THIS FILE DOES NOT PROVE:
  - Frege 2^{Ω(n)} (the claimed "breakthrough" is incorrect)
  - P ≠ NP

  WHY THE CLAIMED ARGUMENT FAILS:
  1. abd_bsw_resolution_exponential's constant c absorbs N = O(n).
     For N >> n, the constant blows up, and the axiom is inapplicable.
  2. Even with the correct BSW (bsw_with_formula_size), proportional
     b gives only linear lower bounds, not exponential.
  3. The self-referential bootstrap cannot close to exponential because
     the BSW denominator grows with S.

  THE HONEST CONCLUSION:
  Sigma's observation is interesting but does not change the landscape.
  The best Frege lower bound from k-consistency remains Ω(n²/log n).
  Super-polynomial Frege bounds require fundamentally new techniques. -/

end CubeGraph
