/-
  CubeGraph/IntegerMonodromy.lean

  Integer (ℕ) matrices and the boolean↔ℤ information gap.

  Key result: Boolean matrix composition = Integer composition + thresholding.
  Thresholding discards multiplicities: integer trace counts ALL consistent
  gap selections, while boolean trace only detects EXISTENCE.

  Empirical context (E-META experiment, 2026-03-19):
  - Boolean trace per cycle: 2-7 fixed points
  - Integer trace per cycle: 50-5000 selections
  - Gap ratio: 10-1000× (7-13 bits lost per cycle)

  See: experiments-ml/024/E-META-RESULTS.md
-/

import CubeGraph.BoolMat

namespace CubeGraph

-- ═════════════════════════════════════════════════════════════════════
-- Section 1: NatMat — natural number matrices
-- ═════════════════════════════════════════════════════════════════════

/-- A natural number matrix of size n × n. -/
def NatMat (n : Nat) := Fin n → Fin n → Nat

namespace NatMat

variable {n : Nat}

/-- Sum of a list of naturals. Custom def for clean induction proofs. -/
def listNatSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listNatSum xs

/-- Natural matrix multiplication: (A·B)[i,j] = Σ_k A[i,k]·B[k,j] -/
def mul (A B : NatMat n) : NatMat n :=
  fun i j => listNatSum ((List.finRange n).map fun k => A i k * B k j)

/-- Trace over ℕ: Σ_i M[i,i] -/
def natTrace (M : NatMat n) : Nat :=
  listNatSum ((List.finRange n).map fun i => M i i)

/-- Identity matrix over ℕ -/
def one : NatMat n :=
  fun i j => if i = j then 1 else 0

/-- Embed BoolMat into NatMat: true → 1, false → 0 -/
def ofBool (M : BoolMat n) : NatMat n :=
  fun i j => if M i j then 1 else 0

/-- Threshold NatMat to BoolMat: > 0 → true, 0 → false -/
def toBool (M : NatMat n) : BoolMat n :=
  fun i j => decide (M i j > 0)

/-- Count of true diagonal entries in a BoolMat.
    Unlike BoolMat.trace (Bool = ∃), this counts HOW MANY. -/
def boolTraceCount (M : BoolMat n) : Nat :=
  (List.finRange n).countP fun i => M i i

/-- Sequential composition over ℕ (right fold). -/
def mulSeq : List (NatMat n) → NatMat n
  | [] => one
  | M :: Ms => mul M (mulSeq Ms)

/-- Sequential composition over 𝔹 (right fold). -/
def boolMulSeq : List (BoolMat n) → BoolMat n
  | [] => BoolMat.one
  | M :: Ms => BoolMat.mul M (boolMulSeq Ms)

-- ═════════════════════════════════════════════════════════════════════
-- Section 2: listNatSum lemmas
-- ═════════════════════════════════════════════════════════════════════

@[simp] theorem listNatSum_nil : listNatSum [] = 0 := rfl

@[simp] theorem listNatSum_cons (a : Nat) (t : List Nat) :
    listNatSum (a :: t) = a + listNatSum t := rfl

/-- A sum of naturals is positive iff some element is positive. -/
theorem listNatSum_pos_iff {l : List Nat} :
    listNatSum l > 0 ↔ ∃ x ∈ l, x > 0 := by
  induction l with
  | nil => simp [listNatSum]
  | cons a t ih =>
    simp only [listNatSum_cons]
    constructor
    · intro h
      by_cases ha : a > 0
      · exact ⟨a, .head t, ha⟩
      · have ha0 : a = 0 := by omega
        have ht : listNatSum t > 0 := by omega
        obtain ⟨x, hxt, hxp⟩ := ih.mp ht
        exact ⟨x, .tail a hxt, hxp⟩
    · rintro ⟨x, hx, hxp⟩
      cases hx with
      | head => omega
      | tail _ hxt =>
        have := ih.mpr ⟨x, hxt, hxp⟩
        omega

-- ═════════════════════════════════════════════════════════════════════
-- Section 3: Conversion lemmas
-- ═════════════════════════════════════════════════════════════════════

/-- Helper: convert Bool iff to Bool equality. -/
private theorem bool_ext {a b : Bool} (h : (a = true) ↔ (b = true)) : a = b := by
  cases a <;> cases b <;> simp_all

/-- toBool entry is true iff nat entry is positive. -/
theorem toBool_true_iff (M : NatMat n) (i j : Fin n) :
    toBool M i j = true ↔ M i j > 0 := by
  simp [toBool, decide_eq_true_eq]

/-- Roundtrip: threshold ∘ embed = identity. -/
theorem toBool_ofBool (M : BoolMat n) : toBool (ofBool M) = M := by
  funext i j
  simp only [toBool, ofBool]
  split <;> simp_all

/-- Product of nat values is positive iff both are positive. -/
private theorem nat_mul_pos_iff {a b : Nat} : a * b > 0 ↔ a > 0 ∧ b > 0 := by
  constructor
  · intro h
    constructor
    · cases a with
      | zero => simp at h
      | succ n => omega
    · cases b with
      | zero => simp at h
      | succ n => omega
  · intro ⟨ha, hb⟩
    exact Nat.mul_pos ha hb

-- ═════════════════════════════════════════════════════════════════════
-- Section 4: BRIDGE THEOREM — boolean = integer + threshold
-- ═════════════════════════════════════════════════════════════════════

/-- **General Bridge**: Thresholding integer product = boolean product of thresholds.
    toBool(A ·_ℕ B) = toBool(A) ·_𝔹 toBool(B)

    Boolean multiplication IS integer multiplication with information
    discarded (thresholding kills multiplicities). -/
theorem bridge_general (A B : NatMat n) :
    toBool (mul A B) = BoolMat.mul (toBool A) (toBool B) := by
  funext i j
  apply bool_ext
  simp only [toBool_true_iff, BoolMat.mul, mul]
  rw [listNatSum_pos_iff]
  simp only [List.any_eq_true, Bool.and_eq_true, toBool_true_iff]
  constructor
  · rintro ⟨x, hxm, hxp⟩
    rw [List.mem_map] at hxm
    obtain ⟨k, hk, rfl⟩ := hxm
    exact ⟨k, hk, nat_mul_pos_iff.mp hxp⟩
  · rintro ⟨k, hk, hak, hbk⟩
    refine ⟨A i k * B k j, ?_, Nat.mul_pos hak hbk⟩
    exact List.mem_map.mpr ⟨k, hk, rfl⟩

/-- **Bridge for embedded matrices**: For BoolMat inputs specifically,
    integer composition + threshold = boolean composition. -/
theorem bridge_mul (A B : BoolMat n) :
    toBool (mul (ofBool A) (ofBool B)) = BoolMat.mul A B := by
  rw [bridge_general, toBool_ofBool, toBool_ofBool]

-- ═════════════════════════════════════════════════════════════════════
-- Section 5: TRACE INEQUALITY — the fundamental gap
-- ═════════════════════════════════════════════════════════════════════

/-- Counting positive entries in mapped list ≤ sum of mapped list. -/
theorem countP_fun_le_listNatSum_map {α : Type} (l : List α) (f : α → Nat) :
    l.countP (fun x => decide (f x > 0)) ≤ listNatSum (l.map f) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons, List.map_cons, listNatSum_cons]
    split
    · -- decide (f a > 0) = true → f a ≥ 1
      rename_i ha; rw [decide_eq_true_eq] at ha
      have h1 : 1 ≤ f a := ha
      have h2 := ih
      omega
    · -- decide (f a > 0) = false → f a = 0
      have h2 := ih
      omega

/-- **Trace Inequality (T2)**: Boolean trace count ≤ integer trace.
    |{i : M[i,i] > 0}| ≤ Σ_i M[i,i].
    This IS the information gap: thresholding loses multiplicity. -/
theorem boolTraceCount_le_natTrace (M : NatMat n) :
    boolTraceCount (toBool M) ≤ natTrace M := by
  unfold boolTraceCount natTrace
  show (List.finRange n).countP (fun i => toBool M i i) ≤ _
  simp only [toBool]
  exact countP_fun_le_listNatSum_map (List.finRange n) (fun i => M i i)

/-- On embedded BoolMat, integer trace = boolean trace count (gap is zero on inputs). -/
theorem natTrace_ofBool_eq_boolTraceCount (M : BoolMat n) :
    natTrace (ofBool M) = boolTraceCount M := by
  unfold natTrace boolTraceCount ofBool
  induction (List.finRange n) with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, listNatSum_cons, List.countP_cons]
    split
    · -- M a a = true
      rename_i h; simp [h] at *; omega
    · -- M a a = false
      rename_i h
      simp only [Bool.not_eq_true] at h
      simp [h] at *; omega

-- ═════════════════════════════════════════════════════════════════════
-- Section 6: SEQUENTIAL COMPOSITION — bridge extends to chains
-- ═════════════════════════════════════════════════════════════════════

/-- toBool of NatMat.one = BoolMat.one -/
theorem toBool_one : toBool (one : NatMat n) = BoolMat.one := by
  funext i j
  simp only [toBool, one, BoolMat.one]
  split <;> simp_all

/-- Bridge extends to sequential composition by induction. -/
theorem bridge_compose (Ms : List (BoolMat n)) :
    toBool (mulSeq (Ms.map ofBool)) = boolMulSeq Ms := by
  induction Ms with
  | nil =>
    simp only [List.map_nil, mulSeq, boolMulSeq]
    exact toBool_one
  | cons M rest ih =>
    simp only [List.map_cons, mulSeq, boolMulSeq]
    rw [bridge_general, toBool_ofBool, ih]

/-- General bridge for sequential composition on NatMat. -/
theorem bridge_compose_general (Ms : List (NatMat n)) :
    toBool (mulSeq Ms) = boolMulSeq (Ms.map toBool) := by
  induction Ms with
  | nil =>
    simp only [List.map_nil, mulSeq, boolMulSeq]
    exact toBool_one
  | cons M rest ih =>
    simp only [List.map_cons, mulSeq, boolMulSeq]
    rw [bridge_general, ih]

-- ═════════════════════════════════════════════════════════════════════
-- Section 7: INFORMATION LOSS THEOREM — the main statement
-- ═════════════════════════════════════════════════════════════════════

/-- The composition gap: integer trace of composition ≥ boolean trace count. -/
theorem composition_gap (Ms : List (NatMat n)) :
    boolTraceCount (toBool (mulSeq Ms)) ≤ natTrace (mulSeq Ms) :=
  boolTraceCount_le_natTrace (mulSeq Ms)

/-- For embedded BoolMat: the gap appears at composition, not at input. -/
theorem gap_at_composition (Ms : List (BoolMat n)) :
    -- Before composition: no gap (trace = count for each input)
    (∀ M ∈ Ms, natTrace (ofBool M) = boolTraceCount M)
    -- After composition: gap appears (trace count ≤ trace)
    ∧ boolTraceCount (boolMulSeq Ms) ≤ natTrace (mulSeq (Ms.map ofBool)) := by
  constructor
  · intro M _; exact natTrace_ofBool_eq_boolTraceCount M
  · rw [← bridge_compose]
    exact boolTraceCount_le_natTrace _

/-- **Information Loss Theorem**: Boolean composition is integer composition
    with multiplicity information irreversibly lost.

    For any sequence of boolean transfer matrices:
    1. Boolean composition = threshold of integer composition (bridge)
    2. Boolean trace count ≤ integer trace of composition (gap)
    3. Boolean trace count ≤ n (bounded by matrix size)

    The gap (integer trace − boolean trace count) measures the multiplicities
    invisible to boolean (OR/AND) composition. -/
theorem information_loss (Ms : List (BoolMat n)) :
    -- (1) Bridge: boolean composition = threshold of integer composition
    toBool (mulSeq (Ms.map ofBool)) = boolMulSeq Ms
    -- (2) Gap: boolean trace count ≤ integer trace of composition
    ∧ boolTraceCount (boolMulSeq Ms) ≤ natTrace (mulSeq (Ms.map ofBool))
    -- (3) Bounded: boolean trace count ≤ matrix dimension
    ∧ boolTraceCount (boolMulSeq Ms) ≤ n := by
  refine ⟨bridge_compose Ms, ?_, ?_⟩
  · -- Gap
    rw [← bridge_compose]
    exact boolTraceCount_le_natTrace _
  · -- Bounded by n: countP ≤ length = n
    unfold boolTraceCount
    have h1 : (List.finRange n).countP (fun i => (boolMulSeq Ms) i i) ≤ (List.finRange n).length :=
      List.countP_le_length
    have h2 : (List.finRange n).length = n := by
      unfold List.finRange; exact List.length_ofFn
    omega

end NatMat
end CubeGraph
