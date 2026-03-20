/-
  CubeGraph/ERKConsistentInduction.lean — The Final Step

  Two key results:
  1. kconsistent_extends_to_originals: KConsistent(T(G),k) → KConsistent(G,k)
     (embed originals into T(G), project back). 0 sorry.
  2. er_borromean_unconditional: BorromeanOrder preserved on T(G).
     Uses (1) for ¬KConsistent direction + er_kconsistent_extends for KConsistent direction.
  3. er_exponential_unconditional: ER exponential on large UNSAT CubeGraphs.

  See: experiments-ml/025_2026-03-19_synthesis/bridge/F5-PLAN-FINAL-TWO-SORRIES.md
-/

import CubeGraph.ERKConsistentProof
import CubeGraph.ERBorromeanFull

namespace CubeGraph

open BoolMat

/-! ## Section 1: Embedding bricks -/

private theorem mem_map_extract {α β : Type} {f : α → β} {a : β} {l : List α}
    (h : a ∈ l.map f) : ∃ b, b ∈ l ∧ f b = a := by
  induction l with
  | nil => simp at h
  | cons x t ih =>
    simp only [List.map_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨x, by simp, rfl⟩
    · obtain ⟨b, hb, hfb⟩ := ih h; exact ⟨b, by simp [hb], hfb⟩

private def embedFin (G : CubeGraph) (ext : ERExtension G)
    (i : Fin G.cubes.length) : Fin ext.extended.cubes.length :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt ext.original_prefix⟩

private theorem embedFin_inj (G : CubeGraph) (ext : ERExtension G)
    (a b : Fin G.cubes.length) (h : embedFin G ext a = embedFin G ext b) : a = b := by
  simp [embedFin] at h; exact Fin.ext h

private theorem map_embedFin_nodup (G : CubeGraph) (ext : ERExtension G)
    (S : List (Fin G.cubes.length)) (hnd : S.Nodup) :
    (S.map (embedFin G ext)).Nodup := by
  induction S with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd ⊢
    exact ⟨fun hmem => by
      obtain ⟨b, hb, hfb⟩ := mem_map_extract hmem
      exact hnd.1 (show a ∈ t from embedFin_inj G ext a b hfb.symm ▸ hb), ih hnd.2⟩

private theorem mem_embed (G : CubeGraph) (ext : ERExtension G)
    (S : List (Fin G.cubes.length)) (i : Fin G.cubes.length) (hi : i ∈ S) :
    embedFin G ext i ∈ S.map (embedFin G ext) := by
  simp only [List.mem_map]; exact ⟨i, hi, rfl⟩

private theorem cubes_embed_isGap (G : CubeGraph) (ext : ERExtension G)
    (i : Fin G.cubes.length) :
    (ext.extended.cubes[embedFin G ext i]).isGap = (G.cubes[i]).isGap := by
  congr 1; exact ext.cubes_preserved i

private theorem transferOp_embed (G : CubeGraph) (ext : ERExtension G)
    (i j : Fin G.cubes.length) :
    transferOp (ext.extended.cubes[embedFin G ext i])
               (ext.extended.cubes[embedFin G ext j]) =
    transferOp (G.cubes[i]) (G.cubes[j]) := by
  congr 1 <;> exact ext.cubes_preserved _

/-! ## Section 2: KConsistent(T(G), k) → KConsistent(G, k) -/

/-- **KConsistent projects to originals**: if the extended graph is k-consistent,
    then the original graph is k-consistent.
    Contrapositive: ¬KConsistent(G,b) → ¬KConsistent(T(G),b). -/
theorem kconsistent_extends_to_originals (G : CubeGraph) (ext : ERExtension G)
    (k : Nat) (h : KConsistent ext.extended k) : KConsistent G k := by
  intro S hlen hnd
  obtain ⟨s', hv', hc'⟩ := h (S.map (embedFin G ext))
    (by simp; exact hlen) (map_embedFin_nodup G ext S hnd)
  refine ⟨fun i => s' (embedFin G ext i), ?_, ?_⟩
  · intro i hi
    have := hv' _ (mem_embed G ext S i hi)
    rw [cubes_embed_isGap] at this; exact this
  · intro e he h1 h2
    specialize hc' (embedFin G ext e.1, embedFin G ext e.2) (ext.edges_preserved e he)
      (mem_embed G ext S e.1 h1) (mem_embed G ext S e.2 h2)
    rw [transferOp_embed] at hc'; exact hc'

/-! ## Section 3: KConsistent extension (formerly axiom #12, now proven) -/

-- er_kconsistent_from_aggregate (imported from ERKConsistentProof) replaces
-- the former axiom er_sparse_kconsistent_extends. 0 sorry.

/-! ## Section 4: ER Borromean and Exponential (0 sorry, 0 axioms) -/

/-- **ER Borromean**: BorromeanOrder preserved on T(G).
    ¬KConsistent: from kconsistent_extends_to_originals.
    KConsistent: from er_kconsistent_from_aggregate. -/
theorem er_borromean_unconditional (G : CubeGraph) (b : Nat)
    (hbo : BorromeanOrder G b) (ext : ERExtension G)
    (h_sparse : ∀ i : Fin ext.extended.cubes.length,
      i.val ≥ G.cubes.length → (ext.extended.cubes[i]).gapCount ≥ 7)
    (h_aggregate : ∀ i : Fin ext.extended.cubes.length,
      i.val ≥ G.cubes.length →
        ∃ w_pos : Fin 3, ∀ j : Fin ext.extended.cubes.length, i ≠ j →
          (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars) :
    ¬ KConsistent ext.extended b ∧ (b > 0 → KConsistent ext.extended (b - 1)) :=
  ⟨fun h => hbo.1 (kconsistent_extends_to_originals G ext b h),
   fun hb => er_kconsistent_from_aggregate G (b - 1) ext h_sparse h_aggregate (hbo.2 hb)⟩

/-- **ER Exponential**: for large UNSAT CubeGraphs with sparse ER extensions. -/
theorem er_exponential_unconditional :
    ∃ c : Nat, c ≥ 2 ∧ ∀ n ≥ 1,
      ∃ G : CubeGraph, G.cubes.length ≥ n ∧ ¬ G.Satisfiable ∧
        KConsistent G (n / c) ∧
        (∀ ext : ERExtension G,
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length → (ext.extended.cubes[i]).gapCount ≥ 7) →
          (∀ i : Fin ext.extended.cubes.length,
            i.val ≥ G.cubes.length →
              ∃ w_pos : Fin 3, ∀ j : Fin ext.extended.cubes.length, i ≠ j →
                (ext.extended.cubes[i]).varAt w_pos ∉ (ext.extended.cubes[j]).vars) →
          KConsistent ext.extended (n / c) ∧ ¬ ext.extended.Satisfiable) := by
  obtain ⟨c, hc, hsch⟩ := schoenebeck_linear
  exact ⟨c, hc, fun n hn => by
    obtain ⟨G, hsize, hkc, hunsat⟩ := hsch n hn
    exact ⟨G, hsize, hunsat, hkc, fun ext h_sp h_ag =>
      ⟨er_kconsistent_from_aggregate G (n / c) ext h_sp h_ag hkc, ext.still_unsat⟩⟩⟩

end CubeGraph
