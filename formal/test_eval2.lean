import CubeGraph.ProofComplexityModel
import CubeGraph.SchoenebeckAxiom

namespace CubeGraph

private def schoenebeckAssignment (G : CubeGraph)
    (S : List (Fin G.cubes.length))
    (s : (i : Fin G.cubes.length) → Vertex) : GapAssignment G :=
  fun v => if v.cube ∈ S then decide (v.vertex = s v.cube) else false

-- General: foldl preserves eval=true
private theorem foldl_preserves_true {α : Type} {G : CubeGraph}
    (σ : GapAssignment G) (f : GapFormula G → α → GapFormula G)
    (init : GapFormula G) (ls : List α)
    (hinit : init.eval σ = true)
    (hpres : ∀ acc a, acc.eval σ = true → (f acc a).eval σ = true) :
    (ls.foldl f init).eval σ = true := by
  induction ls generalizing init with
  | nil => exact hinit
  | cons a as ih => exact ih (f init a) (hpres init a hinit)

-- General: foldl becomes true and stays true
-- If at SOME point the step makes it true, all subsequent steps preserve true
private theorem foldl_becomes_true {α : Type} {G : CubeGraph}
    (σ : GapAssignment G) (f : GapFormula G → α → GapFormula G)
    (init : GapFormula G) (ls : List α)
    (hpres : ∀ acc a, acc.eval σ = true → (f acc a).eval σ = true)
    (a₀ : α) (ha₀ : a₀ ∈ ls)
    (htrigger : ∀ acc, (f acc a₀).eval σ = true) :
    (ls.foldl f init).eval σ = true := by
  induction ls generalizing init with
  | nil => exact absurd ha₀ (List.not_mem_nil _)
  | cons a as ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ha₀ with rfl | ha₀'
    · -- a₀ = a: after this step, true; then preserved
      exact foldl_preserves_true σ f (f init a) as (htrigger init) hpres
    · -- a₀ ∈ as: recurse
      exact ih (f init a) ha₀'

-- atLeastOneGap step: if isGap g then disj acc (var ⟨i,g⟩) else acc
-- This preserves true (disj with anything preserves true)
private theorem atLeastOneGap_step_pres (G : CubeGraph)
    (σ : GapAssignment G) (i : Fin G.cubes.length)
    (acc : GapFormula G) (g : Fin 8)
    (hacc : acc.eval σ = true) :
    (if G.cubes[i].isGap g then GapFormula.disj acc (.var ⟨i, g⟩) else acc).eval σ = true := by
  split
  · simp only [GapFormula.eval, Bool.or_eq_true]; exact Or.inl hacc
  · exact hacc

-- atLeastOneGap triggers at g = s(i) when i ∈ S
private theorem atLeastOneGap_triggers (G : CubeGraph)
    (S : List (Fin G.cubes.length))
    (s : (i : Fin G.cubes.length) → Vertex)
    (i : Fin G.cubes.length) (hi : i ∈ S)
    (hgap : G.cubes[i].isGap (s i) = true)
    (acc : GapFormula G) :
    (if G.cubes[i].isGap (s i) then GapFormula.disj acc (.var ⟨i, s i⟩)
     else acc).eval (schoenebeckAssignment G S s) = true := by
  rw [if_pos hgap]
  simp only [GapFormula.eval, Bool.or_eq_true]
  right
  simp only [schoenebeckAssignment, if_pos hi]
  decide

-- atLeastOneGap G i evaluates to true under schoenebeckAssignment when i ∈ S
theorem atLeastOneGap_eval (G : CubeGraph)
    (S : List (Fin G.cubes.length))
    (s : (i : Fin G.cubes.length) → Vertex)
    (i : Fin G.cubes.length)
    (hi : i ∈ S)
    (hgap : G.cubes[i].isGap (s i) = true) :
    (atLeastOneGap G i).eval (schoenebeckAssignment G S s) = true := by
  simp only [atLeastOneGap]
  let σ := schoenebeckAssignment G S s
  -- s(i) ∈ finRange 8 (it's a Fin 8 = Vertex)
  apply foldl_becomes_true σ
    (fun acc g => if G.cubes[i].isGap g then GapFormula.disj acc (.var ⟨i, g⟩) else acc)
    GapFormula.bot (List.finRange 8)
  · exact fun acc g hacc => atLeastOneGap_step_pres G σ i acc g hacc
  · exact s i
  · exact List.mem_finRange (s i)
  · exact fun acc => atLeastOneGap_triggers G S s i hi hgap acc

#check @atLeastOneGap_eval
end CubeGraph
