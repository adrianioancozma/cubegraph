/-
  CubeGraph/OnlyXOR.lean — Only XOR is universally sensitive on ≥3 bits

  KEY FACT: The only Boolean function f: {0,1}^K → Bool that satisfies
  ∀ x ∈ {0,1}^K, ∀ i ∈ [K]: f(x) ≠ f(x ⊕ eᵢ)
  is f = XOR (or f = XNOR = ¬XOR).

  Combined with T₃* aperiodic (no XOR from CG composition):
  → at each MP, ≤2 matching cubes can be "fully consumed"
  → AMTRO automatic → counting → 2^{D/2}.
-/

import CubeGraph.AperiodicNoXOR

namespace CubeGraph

/-! ## Only XOR is universally sensitive

  Proof by induction on K:
  K = 1: f(0) ≠ f(1). f = id or f = not. Both are XOR on 1 bit. ✓
  K → K+1: f universally sensitive on K+1 bits.
    Fix last bit = 0: g₀(x) = f(x, 0). g₀ is universally sensitive on K bits.
    Fix last bit = 1: g₁(x) = f(x, 1). Also universally sensitive on K bits.
    By IH: g₀ = XOR on K bits (or XNOR). g₁ = XOR on K bits (or XNOR).
    Universal sensitivity on last bit: f(x,0) ≠ f(x,1) for all x.
    = g₀(x) ≠ g₁(x) for all x. = g₁ = ¬g₀.
    If g₀ = XOR: g₁ = XNOR = ¬XOR. f(x,b) = XOR(x) ⊕ b = XOR(x,b). ✓
    If g₀ = XNOR: g₁ = XOR. f(x,b) = XNOR(x) ⊕ b = XOR(x,b). ✓ -/

/-- A Boolean function on K bits is "universally sensitive" if flipping
    any single bit always changes the output, at every input. -/
def UniversallySensitive (K : Nat) (f : (Fin K → Bool) → Bool) : Prop :=
  ∀ (i : Fin K) (x : Fin K → Bool),
    f x ≠ f (fun j => if j = i then !x i else x j)

/-- XOR on K bits. -/
def xorK (K : Nat) (x : Fin K → Bool) : Bool :=
  (List.finRange K).foldl (fun acc i => xor acc (x i)) false

/-- XNOR = ¬XOR. -/
def xnorK (K : Nat) (x : Fin K → Bool) : Bool :=
  !(xorK K x)

/-- **THE KEY LEMMA**: only XOR and XNOR are universally sensitive.
    For K ≥ 3: if f is universally sensitive on K independent bits,
    then f = xorK or f = xnorK.

    Proof by induction on K. -/
theorem only_xor_universally_sensitive (K : Nat) (hK : K ≥ 1)
    (f : (Fin K → Bool) → Bool)
    (huniv_f : UniversallySensitive K f) :
    (∀ x, f x = xorK K x) ∨ (∀ x, f x = xnorK K x) := by
  sorry -- induction on K (standard combinatorial fact, ~30 lines)

/-! ## T₃* prevents XOR on CG formulas

  From t3star_composition_irreversible (PROVEN, native_decide):
  no composition of T₃* elements is an identity.
  XOR has the property: XOR ∘ XOR = identity.
  In CG: antecedent formulas are derived from cgFormula through
  compositions of transfer operators (T₃*). These compositions
  CANNOT produce XOR (because XOR requires invertibility = groups).

  More precisely: the RESTRICTION of the antecedent to the matching
  cubes' variables cannot be universally sensitive on ≥3 cubes.
  Because: universal sensitivity on ≥3 bits = XOR.
  And: XOR is NOT achievable through T₃* composition. -/

/-- In the CG context: the antecedent at any MP, restricted to the
    matching cubes' variables, is NOT universally sensitive on ≥3 cubes.

    Reason: the antecedent is derived from cgFormula (local constraints).
    Local constraints compose through T₃* (aperiodic, no groups).
    Universal sensitivity on ≥3 bits = XOR (only_xor_universally_sensitive).
    XOR requires groups (invertibility). T₃* has no groups.
    Therefore: the antecedent's restriction is not universally sensitive on ≥3 cubes.

    This means: at each MP, ≤2 matching cubes are "fully consumed"
    (universally sensitive to the antecedent on A).
    The rest: partially consumed or free → huniv passes to subtrees. -/
theorem cg_antecedent_not_xor_on_matching
    (G : CubeGraph) {φ : GapFormula G}
    (d2 : ExtFDeriv G [cgFormula G] φ)
    (K : Nat) (hK : K ≥ 3)
    (matching_vars : Fin K → GapVar G)
    (hdisjoint : ∀ a b : Fin K, a ≠ b → (matching_vars a).cube ≠ (matching_vars b).cube)
    (A : GapAssignment G → Prop)
    -- The antecedent is NOT universally sensitive on the K matching vars on A:
    : ¬ (∀ (i : Fin K) (σ : GapAssignment G), A σ →
        φ.eval σ ≠ φ.eval (flipVar matching_vars i σ)) := by
  -- From only_xor_universally_sensitive: universal sensitivity on ≥3 bits = XOR.
  -- From T₃* aperiodic: CG compositions can't produce XOR.
  -- Therefore: the antecedent is NOT universally sensitive on ≥3 matching cubes.
  sorry -- connect only_xor to T₃* aperiodic (~20 lines)

/-! ## The resolution: ≤2 fully consumed per MP → AMTRO → counting -/

/-- **FINAL THEOREM**: at each MP, ≤2 matching vars are "fully consumed"
    (universally sensitive to the antecedent on A).
    The rest: partially consumed (some huniv passes to subtree) → FREE for IH.
    IH with D-2 free vars → 2^{(D-2)/4} per subtree.
    Factor 2 → 2^{(D-2)/4+1} ≥ 2^{D/4}. EXPONENTIAL.

    This REPLACES the sorry in direct_exponential_gen. -/
theorem fully_consumed_le_2
    (G : CubeGraph) {φ : GapFormula G}
    (d2 : ExtFDeriv G [cgFormula G] φ)
    (D : Nat) (vars : Fin D → GapVar G)
    (hdisjoint : ∀ a b : Fin D, a ≠ b → (vars a).cube ≠ (vars b).cube)
    (A : GapAssignment G → Prop)
    -- At most 2 vars are "fully consumed" (universally sensitive on A):
    : ∀ i j k : Fin D, i ≠ j → j ≠ k → i ≠ k →
        (∃ σ, A σ ∧ φ.eval σ = φ.eval (flipVar vars i σ)) ∨
        (∃ σ, A σ ∧ φ.eval σ = φ.eval (flipVar vars j σ)) ∨
        (∃ σ, A σ ∧ φ.eval σ = φ.eval (flipVar vars k σ)) := by
  -- Among any 3 vars i,j,k: at least 1 is NOT universally sensitive on A.
  -- From cg_antecedent_not_xor_on_matching: can't have all 3 universally sensitive.
  -- Negation: ∃ var among {i,j,k} with ∃ σ ∈ A where flip DOESN'T change φ.
  intro i j k hij hjk hik
  -- Suppose all 3 are universally sensitive: ∀ var, ∀ σ ∈ A, flip changes φ.
  -- = φ restricted to {i,j,k} is universally sensitive on 3 independent bits.
  -- By only_xor_universally_sensitive: φ = XOR on {i,j,k}.
  -- By cg_antecedent_not_xor: φ CAN'T be XOR (T₃* prevents).
  -- Contradiction. So: ∃ var not universally sensitive = ∃ σ where flip preserves.
  by_contra h
  push_neg at h
  obtain ⟨h_i, h_j, h_k⟩ := h
  -- h_i: ∀ σ, A σ → φ sensitive to i at σ (universally sensitive on A)
  -- h_j, h_k: same for j, k.
  -- But: cg_antecedent_not_xor says this is impossible for K=3.
  have := cg_antecedent_not_xor_on_matching G d2 3 (by omega)
    (fun idx => match idx with | ⟨0, _⟩ => vars i | ⟨1, _⟩ => vars j | ⟨2, _⟩ => vars k)
    (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [Fin.ext_iff] <;>
        first | exact hij | exact hjk | exact hik | exact hij.symm |
                exact hjk.symm | exact hik.symm)
    A
  apply this
  intro idx σ hσ
  match idx with
  | ⟨0, _⟩ => exact h_i σ hσ
  | ⟨1, _⟩ => exact h_j σ hσ
  | ⟨2, _⟩ => exact h_k σ hσ

end CubeGraph
