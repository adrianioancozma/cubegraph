/-
  CubeGraph/TrivialPolymorphism.lean
  T10: Trivial Polymorphism — single gap forces projection.

  When a cube has exactly one gap, any binary operation that preserves
  gaps must return that gap. The operation is trivial (constant on the
  unique valid input). No information can be created or combined.

  See: TrivialSection.lean (constant gap → SAT)
  See: IdempotenceBarrier.lean (T6: M²=M, propagation stagnates)
  See: DimensionThreshold.lean (T9: k=2 has majority, k=3 doesn't)
  See: experiments-ml/021_.../T10-PLAN.md (plan)
  See: experiments-ml/021_.../MICRO-MACRO-BRIDGE.md (trivial polymorphism = bridge saturates)
-/

import CubeGraph.TrivialSection

namespace CubeGraph

/-! ## Section 1: Definitions -/

/-- A cube has a single gap at vertex g: g is a gap and nothing else is. -/
def SingleGap (c : Cube) (g : Vertex) : Prop :=
  c.isGap g = true ∧ ∀ v : Vertex, v ≠ g → c.isGap v = false

/-- A binary operation preserves gaps of a cube. -/
def PreservesGap (c : Cube) (f : Vertex → Vertex → Vertex) : Prop :=
  ∀ g₁ g₂ : Vertex, c.isGap g₁ = true → c.isGap g₂ = true →
    c.isGap (f g₁ g₂) = true

/-! ## Section 2: Main Theorem -/

/-- **Trivial Polymorphism**: single gap g ⇒ f(g,g) = g.
    The only valid input pair is (g,g), and the output must be a gap, so = g. -/
theorem single_gap_forces_fixed (c : Cube) (g : Vertex)
    (f : Vertex → Vertex → Vertex)
    (hsingle : SingleGap c g) (hpres : PreservesGap c f) :
    f g g = g := by
  have hfgg : c.isGap (f g g) = true := hpres g g hsingle.1 hsingle.1
  -- f(g,g) must be a gap. g is the only gap. So f(g,g) = g.
  apply Classical.byContradiction
  intro h_ne
  have hfalse := hsingle.2 (f g g) h_ne
  rw [hfalse] at hfgg
  exact absurd hfgg Bool.false_ne_true

/-- **Corollary**: any gap inputs g₁, g₂ must equal g, so f(g₁,g₂) = g. -/
theorem single_gap_all_inputs (c : Cube) (g : Vertex)
    (f : Vertex → Vertex → Vertex)
    (hsingle : SingleGap c g) (hpres : PreservesGap c f)
    (g₁ g₂ : Vertex) (hg₁ : c.isGap g₁ = true) (hg₂ : c.isGap g₂ = true) :
    f g₁ g₂ = g := by
  -- g₁ = g (only gap)
  have heq₁ : g₁ = g := by
    apply Classical.byContradiction; intro h
    have := hsingle.2 g₁ h; rw [this] at hg₁; exact absurd hg₁ Bool.false_ne_true
  have heq₂ : g₂ = g := by
    apply Classical.byContradiction; intro h
    have := hsingle.2 g₂ h; rw [this] at hg₂; exact absurd hg₂ Bool.false_ne_true
  rw [heq₁, heq₂]
  exact single_gap_forces_fixed c g f hsingle hpres

/-! ## Section 3: Concrete Witness -/

/-- A cube with exactly one gap: vars (1,2,3), gapMask = 1 (only vertex 0). -/
private def singleGapCube : Cube where
  var₁ := 1
  var₂ := 2
  var₃ := 3
  var₁_pos := by omega
  var₂_pos := by omega
  var₃_pos := by omega
  vars_distinct := by decide
  gapMask := ⟨1, by omega⟩
  gaps_nonempty := by decide

/-- All 8 isGap values of singleGapCube, precomputed. -/
private theorem singleGapCube_gaps :
    singleGapCube.isGap ⟨0, by omega⟩ = true ∧
    singleGapCube.isGap ⟨1, by omega⟩ = false ∧
    singleGapCube.isGap ⟨2, by omega⟩ = false ∧
    singleGapCube.isGap ⟨3, by omega⟩ = false ∧
    singleGapCube.isGap ⟨4, by omega⟩ = false ∧
    singleGapCube.isGap ⟨5, by omega⟩ = false ∧
    singleGapCube.isGap ⟨6, by omega⟩ = false ∧
    singleGapCube.isGap ⟨7, by omega⟩ = false := by native_decide

/-- singleGapCube has a single gap at vertex 0. -/
private theorem singleGapCube_single : SingleGap singleGapCube ⟨0, by omega⟩ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := singleGapCube_gaps
  exact ⟨h0, fun v hne => by
    have hne_val : v.val ≠ 0 := fun h => hne (Fin.ext h)
    -- Rewrite v as ⟨v.val, v.isLt⟩ and case split on v.val
    obtain ⟨val, hlt⟩ := v
    -- val ∈ {1,...,7}
    match val, hlt with
    | 0, _ => exact absurd rfl hne_val
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4
    | 5, _ => exact h5
    | 6, _ => exact h6
    | 7, _ => exact h7⟩

/-- Any gap-preserving operation on singleGapCube returns vertex 0. -/
theorem single_gap_witness (f : Vertex → Vertex → Vertex)
    (hpres : PreservesGap singleGapCube f) :
    f ⟨0, by omega⟩ ⟨0, by omega⟩ = ⟨0, by omega⟩ :=
  single_gap_forces_fixed singleGapCube ⟨0, by omega⟩ f singleGapCube_single hpres

/-! ## Section 4: Connection to Satisfiability -/

/-- If every cube has a single gap g and all are compatible, → SAT via trivial section. -/
theorem all_single_gaps_sat (G : CubeGraph) (g : Vertex)
    (hsingle : ∀ i : Fin G.cubes.length, SingleGap (G.cubes[i]) g)
    (hcompat : ∀ e ∈ G.edges, transferOp (G.cubes[e.1]) (G.cubes[e.2]) g g = true) :
    G.Satisfiable :=
  trivial_section_sat G g ⟨fun i => (hsingle i).1, hcompat⟩

/-! ## Section 5: Summary -/

/-- **Summary**: single-gap cubes have trivial polymorphism landscape.
    Every gap-preserving binary operation is the constant function g. -/
theorem polymorphism_trivial_summary :
    ∃ (c : Cube) (g : Vertex),
      SingleGap c g ∧
      ∀ f : Vertex → Vertex → Vertex,
        PreservesGap c f → f g g = g :=
  ⟨singleGapCube, ⟨0, by omega⟩, singleGapCube_single,
   fun f hpres => single_gap_forces_fixed _ _ f singleGapCube_single hpres⟩

end CubeGraph
