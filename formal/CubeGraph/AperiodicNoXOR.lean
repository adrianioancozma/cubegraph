/-
  CubeGraph/AperiodicNoXOR.lean — T₃* algebraic properties + direct exponential (Path 1)

  Docs: experiments-ml/051_2026-04-09_independent-set-path/GAP-ANALYSIS.md
  See also: CubeGraph/CycleResonance.lean (Path 2)
            CubeGraph/DoubleNetwork.lean (double network infrastructure)
            formal/PROOF-CHAIN.md (main chain, 0 sorry with SEPM)

  T₃* = closure of transfer operators under Boolean matrix multiplication.
  |T₃*| = 28 elements (computed via native_decide).

  KEY PROPERTIES (all proven via native_decide):
  1. No product is a two-sided identity
  2. No square acts as identity
  3. Every composition is irreversible (no left-identity products)

  DIRECT EXPONENTIAL (Path 1):
  At each mixed MP: K cubes consumed, D-K insensitive vars pass huniv.
  "Only XOR + T₃*" gives +1 bonus var when K ≥ 3.
  Recursion: f(D) ≥ 2·f(D - effective_K).
  Combined: d.leaves ≥ 2^{D/4}.
-/

import CubeGraph.FourElements
import CubeGraph.TransferMonoid

namespace CubeGraph

/-! ## T₃* algebraic properties (all PROVEN via native_decide) -/

/-- No product in T₃* is a two-sided identity. -/
theorem t3star_no_product_identity :
    (List.finRange 28).all (fun a =>
      (List.finRange 28).all (fun b =>
        !(List.finRange 28).all (fun m =>
          T3Star.mul (T3Star.mul a b) m == m &&
          T3Star.mul m (T3Star.mul a b) == m))) = true := by native_decide

/-- Every element of T₃* satisfies: M² ≠ identity-like. -/
theorem t3star_square_not_identity :
    (List.finRange 28).all (fun m =>
      !(List.finRange 28).all (fun x =>
        T3Star.mul (T3Star.mul m m) x == x)) = true := by native_decide

/-- The composition of ANY two elements is not a left-identity. -/
theorem t3star_composition_irreversible :
    (List.finRange 28).all (fun a =>
      (List.finRange 28).all (fun b =>
        (List.finRange 28).any (fun m =>
          !(T3Star.mul (T3Star.mul a b) m == m)))) = true := by native_decide

/-! ## Direct exponential bound

  The counting argument (counting_k2, PROVEN) gives:
    huniv + AMTRO → d.leaves ≥ 2^{D/2}

  AMTRO says: among any 3 D-vars, ≥1 insensitive to the antecedent on A.
  AMTRO follows from SEPM (K ≤ 2 cubes per MP).

  WITHOUT SEPM: K can be ≥ 3. The "only XOR + T₃*" argument:
  - Among K ≥ 3 D-cubes, if ALL were "universally sensitive to φ on A_L":
    φ restricted to those cubes = XOR (the only universally sensitive function)
  - T₃* aperiodic → can't produce XOR from CG composition
  - Therefore: ≤2 of K cubes are universally sensitive on A_L
  - The rest (≥1 for K ≥ 3) have PARTIAL sensitivity:
    ∃ σ ∈ A_L where flip preserves φ true → that σ stays in A_L
    → huniv passes to d1 for that cube on a restricted A-set

  This gives: d1 has huniv for (D-K) insensitive + 1 bonus = D-K+1 vars.
  Recursion: f(D) ≥ 2·f(D-(K-1)) for K ≥ 3.
  Effective consumption: K-1 instead of K. Saves 1 per level.

  For K ≤ 5: effective ≤ 4. (D-4)/4 + 1 ≥ D/4. ✓
  For K ≥ 6: effective ≥ 5. Need deeper argument (iterated bonus or
  double network structure). -/

/-- **DIRECT EXPONENTIAL**: huniv → d.leaves ≥ 2^{D/4}.
    Structural induction with var deletion + "only XOR + T₃*" bonus.

    At each mixed MP with K relevant D-cubes:
    - D-K insensitive vars pass huniv (derived_insensitive_to_non_S)
    - For K ≥ 3: "only XOR" gives +1 bonus var (T₃* prevents XOR)
    - IH on both subtrees with D-K+1 vars (or D-K for K ≤ 2)
    - d.leaves ≥ 2·2^{(D-K+bonus)/4} ≥ 2^{D/4} -/
theorem direct_exponential_gen
    {ψ : GapFormula G}
    (d : ExtFDeriv G [cgFormula G] ψ) :
    ∀ (A : GapAssignment G → Prop)
      (hA_ne : ∃ σ, A σ)
      (hA_false : ∀ σ, A σ → ψ.eval σ = false)
      (hunsat : ∀ σ, (cgFormula G).eval σ = false)
      (D : Nat) (vars : Fin D → GapVar G)
      (hcubes_disjoint : ∀ a b : Fin D, a ≠ b → (vars a).cube ≠ (vars b).cube)
      (hA_closed : ∀ (i : Fin D) (σ : GapAssignment G), A σ → A (flipVar vars i σ))
      (huniv : ∀ (i : Fin D) (σ : GapAssignment G) (hσ : A σ),
        (d.falseLeafIdx σ (hA_false σ hσ)).val ≠
        (d.falseLeafIdx (flipVar vars i σ) (hA_false _ (hA_closed i σ hσ))).val),
      d.leaves ≥ 2 ^ (D / 4) := by
  induction d with
  | fax h =>
    intro A hA_ne hA_false _ _ _ _ _ _
    exfalso; obtain ⟨σ, hσ⟩ := hA_ne
    exact absurd (ext_frege_axiom_eval_true h σ) (by rw [hA_false σ hσ]; simp)
  | hyp _ =>
    intro A hA_ne hA_false _ D vars _ _ huniv
    cases D with
    | zero => simp; exact ExtFDeriv.leaves_pos _
    | succ D' =>
      exfalso; obtain ⟨σ, hσ⟩ := hA_ne
      exact huniv ⟨0, by omega⟩ σ hσ (by simp [ExtFDeriv.falseLeafIdx])
  | @mp φ_ant ψ_mp d1 d2 ih1 ih2 =>
    intro A hA_ne hA_false hunsat D vars hcubes_disjoint hA_closed huniv
    cases D with
    | zero => simp; exact ExtFDeriv.leaves_pos _
    | succ D' =>
      -- Case 1: all left (φ always true on A)
      by_cases h_all_true : ∀ σ, A σ → φ_ant.eval σ = true
      · have h1 := ih1 A hA_ne
          (fun σ hσ => impl_eval_false_of (h_all_true σ hσ) (hA_false σ hσ))
          hunsat (D' + 1) vars hcubes_disjoint hA_closed
          (fun i σ hσ => by
            have hd := huniv i σ hσ
            rw [falseLeafIdx_mp_left_val (hA_false σ hσ) (h_all_true σ hσ)] at hd
            rw [falseLeafIdx_mp_left_val (hA_false _ (hA_closed i σ hσ))
              (h_all_true _ (hA_closed i σ hσ))] at hd; exact hd)
        have := d2.leaves_pos; simp only [ExtFDeriv.leaves]; omega
      · -- Case 2: all right (φ always false on A)
        by_cases h_all_false : ∀ σ, A σ → φ_ant.eval σ = false
        · have h2 := ih2 A hA_ne (fun σ hσ => h_all_false σ hσ)
            hunsat (D' + 1) vars hcubes_disjoint hA_closed
            (fun i σ hσ => by
              have hd := huniv i σ hσ
              rw [falseLeafIdx_mp_right_val (hA_false σ hσ) (h_all_false σ hσ)] at hd
              rw [falseLeafIdx_mp_right_val (hA_false _ (hA_closed i σ hσ))
                (h_all_false _ (hA_closed i σ hσ))] at hd; omega)
          have := d1.leaves_pos; simp only [ExtFDeriv.leaves]; omega
        · -- Case 3: mixed. ∃ σ_true ∈ A with φ true, ∃ σ_false ∈ A with φ false.
          push_neg at h_all_true h_all_false
          obtain ⟨σ_f, hσ_f, hφ_f⟩ := h_all_true
          obtain ⟨σ_t, hσ_t, hφ_t⟩ := h_all_false
          have hφ_f' : φ_ant.eval σ_f = false := by
            cases h : φ_ant.eval σ_f with | true => exact absurd h hφ_f | false => rfl
          have hφ_t' : φ_ant.eval σ_t = true := by
            cases h : φ_ant.eval σ_t with | true => rfl | false => exact absurd h hφ_t
          -- 3a: 0 vars relevant on A → pass to A_L with all vars
          by_cases h_no_rel : ∀ (i : Fin (D' + 1)) (σ : GapAssignment G),
              A σ → φ_ant.eval σ = φ_ant.eval (flipVar vars i σ)
          · let A_L := fun σ => A σ ∧ φ_ant.eval σ = true
            have h1 := ih1 A_L ⟨σ_t, hσ_t, hφ_t'⟩
              (fun σ ⟨hσ, hφ⟩ => impl_eval_false_of hφ (hA_false σ hσ))
              hunsat (D' + 1) vars hcubes_disjoint
              (fun i σ ⟨hσ, hφ⟩ => ⟨hA_closed i σ hσ,
                (h_no_rel i σ hσ).symm.trans hφ⟩)
              (fun i σ ⟨hσ, hφ⟩ => by
                have hφ' := (h_no_rel i σ hσ) ▸ hφ
                have hd := huniv i σ hσ
                rw [falseLeafIdx_mp_left_val (hA_false σ hσ) hφ,
                    falseLeafIdx_mp_left_val (hA_false _ (hA_closed i σ hσ)) hφ'] at hd
                exact hd)
            have := d2.leaves_pos; simp only [ExtFDeriv.leaves]; omega
          · -- 3b: ≥1 relevant var. Drop it. IH on both subtrees.
            push_neg at h_no_rel
            obtain ⟨i₀, σ_rel, hσ_rel, hφ_rel⟩ := h_no_rel
            -- All other vars insensitive to φ on A:
            -- This is where AMTRO/SEPM enters. With SEPM: guaranteed.
            -- Without SEPM: we use the "only XOR + T₃*" argument.
            -- For now: we drop i₀ and handle insensitive vars.
            -- The bound: among any 2 remaining vars, ≥1 insensitive to φ on A.
            -- This needs: AtMostTwoRelevantOn (from SEPM or from "only XOR + T₃*").
            --
            -- KEY CLAIM (from CG structure):
            -- At most 2 of the D vars are "universally sensitive" to φ on A.
            -- A var is "universally sensitive" if ∀ σ ∈ A, flip changes φ.
            -- "Only XOR": universal sensitivity on ≥3 independent bits = XOR.
            -- T₃* aperiodic: can't produce XOR from CG composition.
            -- Therefore: ≤2 universally sensitive → AMTRO.
            --
            -- With AMTRO: counting_k2 gives 2^{D/2} (already proven).
            -- Here we show the connection: AMTRO from "only XOR + T₃*".
            -- The sorry marks the exact gap: connecting T₃* to the antecedent.
            sorry

/-- Specialization to d : ExtFDeriv G [cgFormula G] .bot. -/
theorem direct_exponential_from_huniv
    (G : CubeGraph)
    (d : ExtFDeriv G [cgFormula G] .bot)
    (D : Nat) (vars : Fin D → GapVar G)
    (hcubes_disjoint : ∀ a b : Fin D, a ≠ b → (vars a).cube ≠ (vars b).cube)
    (hunsat : ∀ σ, (cgFormula G).eval σ = false)
    (huniv : ∀ (i : Fin D) (σ : GapAssignment G),
      d.botLeafIdx σ ≠ d.botLeafIdx (fun w => if w = vars i then !σ (vars i) else σ w))
    : d.leaves ≥ 2 ^ (D / 4) := by
  exact direct_exponential_gen d (fun _ => True) ⟨fun _ => false, trivial⟩
    (fun _ _ => by simp [GapFormula.eval]) hunsat D vars hcubes_disjoint
    (fun _ _ _ => trivial)
    (fun i σ _ => by intro heq; apply huniv i σ; exact Fin.ext heq)

end CubeGraph
