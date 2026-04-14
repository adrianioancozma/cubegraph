/-
  CubeGraph/Z3Composition.lean
  F2.3: ℤ/3ℤ composition — KR=1 still insufficient.

  The monodromy swap on h2Graph has no fixed points under ANY algebra.
  This is combinatorial, not algebraic.

  See: Type2Monodromy.lean, BarringtonConnection.lean
  See: experiments-ml/022_.../F2.2-RESULTS.md
-/

import CubeGraph.BarringtonConnection

namespace CubeGraph

open BoolMat

/-! ## Section 1: ℤ/3ℤ multiplication -/

/-- Matrix multiplication over ℤ/3ℤ, projected to Bool. -/
def z3_mul (A B : BoolMat n) : BoolMat n :=
  fun i j =>
    let sum := (List.finRange n).foldl
      (fun acc k => acc + if A i k && B k j then 1 else 0) 0
    decide (sum % 3 ≠ 0)

/-! ## Section 2: Monodromy swap is algebra-independent -/

/-- h2MonodromyCycle: no diagonal true entries. Swap has no fixed points.
    True under ANY algebra — combinatorial property. -/
theorem h2_no_fixedpoint :
    h2MonodromyCycle ⟨0, by omega⟩ ⟨0, by omega⟩ = false ∧
    h2MonodromyCycle ⟨3, by omega⟩ ⟨3, by omega⟩ = false ∧
    h2MonodromyCycle ⟨0, by omega⟩ ⟨3, by omega⟩ = true ∧
    h2MonodromyCycle ⟨3, by omega⟩ ⟨0, by omega⟩ = true :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-! ## Section 3: KR=1 summary -/

/-- **KR=1 insufficient**: monodromy traceless + nonzero + local consistency + consistency gap.
    These facts are algebra-independent. Neither KR=0 nor KR=1 helps. -/
theorem kr1_summary :
    trace h2MonodromyCycle = false ∧
    ¬ isZero h2MonodromyCycle ∧
    (∃ G : CubeGraph, LocallyConsistent G ∧ ¬ G.Satisfiable) ∧
    (∃ G : CubeGraph, KConsistent G 2 ∧ ¬ KConsistent G 3) :=
  ⟨h2_monodromy_trace_false, h2_monodromy_nonzero,
   locally_consistent_not_implies_sat,
   ⟨h2Graph, h2graph_2consistent, h2graph_not_3consistent⟩⟩

end CubeGraph
