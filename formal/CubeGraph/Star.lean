/-
  CubeGraph/Star.lean

  The Star: the fundamental object of CubeGraph.

  A Star is a cube (center) together with all its connections (arms).
  N cubes form N stars, each with 1 to N-1 arms. At critical density:
  N ≈ 82 stars, each with ≈ 32 arms.

  SAT = choose one gap per star such that all connected arms agree.

  The star captures the LOCAL perspective: what does the world look like
  from one cube? It sees its 7 gaps and the transfer operators to all
  its neighbors. The global problem is assembling N local perspectives
  into one coherent picture.

  From the symmetry analysis (CubeSymmetriesGroup.lean):
  - 1 star alone:     6 of 48 cube symmetries survive (stabilizer of forbidden vertex)
  - 2 connected stars: 2 survive
  - 3 stars (Stella):  1 survives (identity only)
  - N stars at ρ_c:    1 (completely rigid — no gap interchangeable with another)

  Dependencies: Basic.lean (Cube, CubeGraph, transferOp)
  See: experiments-ml/027_2026-03-24_star-analysis/SESSION-SUMMARY.md
-/

import CubeGraph.Basic

namespace CubeGraph

/-! ## Section 1: Star Definition -/

/-- An arm of a star: a connection to a neighbor cube via a transfer operator. -/
structure Star.Arm (G : CubeGraph) where
  /-- Index of the neighbor cube -/
  neighbor : Fin G.cubes.length
  /-- The edge direction (center, neighbor) -/
  edge_mem : ∃ e ∈ G.edges, (e.1 = center ∧ e.2 = neighbor) ∨
                              (e.1 = neighbor ∧ e.2 = center)
  /-- Index of the center cube (stored for the edge_mem constraint) -/
  center : Fin G.cubes.length

/-- A Star: a center cube with all its arms (connections to neighbors).
    This is the LOCAL view of the CubeGraph from one cube's perspective. -/
structure Star (G : CubeGraph) where
  /-- Index of the center cube -/
  center : Fin G.cubes.length
  /-- Indices of all neighbor cubes -/
  neighbors : List (Fin G.cubes.length)
  /-- All neighbors are actually connected to center -/
  neighbors_connected : ∀ j ∈ neighbors,
    (center, j) ∈ G.edges ∨ (j, center) ∈ G.edges

/-- The center cube of a star. -/
def Star.cube (s : Star G) : Cube := G.cubes[s.center]

/-- The degree (number of arms) of a star. -/
def Star.degree (s : Star G) : Nat := s.neighbors.length

/-- The gap set of the center cube (the fiber). -/
def Star.gaps (s : Star G) : List Vertex :=
  (List.finRange 8).filter (fun v => s.cube.isGap v)

/-- The fiber size (number of choices at this star). -/
def Star.fiberSize (s : Star G) : Nat := s.gaps.length

/-- The transfer operator from center to neighbor j. -/
def Star.transferTo (s : Star G) (j : Fin G.cubes.length) : BoolMat 8 :=
  transferOp s.cube (G.cubes[j])

/-! ## Section 2: Building Stars from a CubeGraph -/

/-- Extract the star centered at cube i from a CubeGraph. -/
def starAt (G : CubeGraph) (i : Fin G.cubes.length) : Star G where
  center := i
  neighbors := (List.finRange G.cubes.length).filter (fun j =>
    i ≠ j ∧ ((i, j) ∈ G.edges ∨ (j, i) ∈ G.edges))
  neighbors_connected := by
    intro j hj
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hj
    exact hj.2

/-- All stars of a CubeGraph. -/
def allStars (G : CubeGraph) : List (Star G) :=
  (List.finRange G.cubes.length).map (starAt G)

/-- The number of stars equals the number of cubes. -/
theorem allStars_length (G : CubeGraph) :
    (allStars G).length = G.cubes.length := by
  simp [allStars]

/-! ## Section 3: Star-Local Consistency

  A gap g at star s is LOCALLY viable if it has at least one compatible
  gap in every neighbor. This is arc consistency from the star's perspective. -/

/-- Gap g at star s has support in neighbor j. -/
def Star.hasSupport (s : Star G) (g : Vertex) (j : Fin G.cubes.length) : Bool :=
  (List.finRange 8).any (fun g' => s.transferTo j g g')

/-- Gap g at star s is star-viable: has support in ALL neighbors. -/
def Star.viable (s : Star G) (g : Vertex) : Bool :=
  s.cube.isGap g && s.neighbors.all (fun j => s.hasSupport g j)

/-- The viable gaps of a star (gaps with full support in all directions). -/
def Star.viableGaps (s : Star G) : List Vertex :=
  (List.finRange 8).filter (fun v => s.viable v)

/-! ## Section 4: Star-Level SAT

  SAT from the star perspective: choose one gap per star, all arms agree. -/

/-- A star selection: one gap per star. -/
def StarSelection (G : CubeGraph) := (i : Fin G.cubes.length) → Vertex

/-- A star selection is valid: each choice is a gap of that star's center. -/
def validStarSelection (G : CubeGraph) (s : StarSelection G) : Prop :=
  ∀ i : Fin G.cubes.length, (G.cubes[i]).isGap (s i) = true

/-- A star selection is compatible: all arms agree. -/
def compatibleStarSelection (G : CubeGraph) (s : StarSelection G) : Prop :=
  ∀ e ∈ G.edges, transferOp (G.cubes[e.1]) (G.cubes[e.2]) (s e.1) (s e.2) = true

/-- Star selection = gap selection. The two views are identical. -/
theorem star_eq_gap_selection (G : CubeGraph) :
    (∃ s : StarSelection G, validStarSelection G s ∧ compatibleStarSelection G s)
    ↔ G.Satisfiable := by
  constructor
  · intro ⟨s, hv, hc⟩; exact ⟨s, hv, hc⟩
  · intro ⟨s, hv, hc⟩; exact ⟨s, hv, hc⟩

/-! ## Section 5: The Rigidity Theorem

  At critical density, after ≥ 3 connected stars, the system is completely
  rigid: no non-trivial symmetry preserves all gap masks simultaneously.

  From CubeSymmetriesGroup.lean: symmetry_breaking_chain gives 48 → 6 → 2 → 1.

  The number of "effective choices" at each star is its fiber size (≈ 7),
  but the arms constrain choices across stars. With zero residual symmetry,
  there are no shortcuts: every gap is distinguishable from every other gap,
  and every choice has unique consequences.

  The SEARCH SPACE is ∏ᵢ fiberSize(starᵢ) ≈ 7^N.
  The SYMMETRY REDUCTION is trivial (factor 1).
  The LOCAL CONSTRAINT REDUCTION (arc consistency) is also trivial
  (99.5% of gaps survive — from experiment 027 star analysis).

  This is the geometric content of NP-hardness:
  N rigid stars, 7 choices each, no symmetry, no local shortcut. -/

/-- The total search space is the product of fiber sizes. -/
def searchSpace (G : CubeGraph) : Nat :=
  (allStars G).foldl (fun acc s => acc * s.fiberSize) 1

/-- Auxiliary: foldl product with init a, factors ≥ k → result ≥ a * k^length. -/
private theorem foldl_mul_ge {α : Type} :
    ∀ (l : List α) (f : α → Nat) (k a : Nat),
    (∀ x ∈ l, f x ≥ k) →
    l.foldl (fun acc x => acc * f x) a ≥ a * k ^ l.length := by
  intro l
  induction l with
  | nil => intros; simp
  | cons hd tl ih =>
    intro f k a hf
    simp only [List.foldl, List.length_cons]
    have hhd : f hd ≥ k := hf hd (.head _)
    have htl : ∀ x ∈ tl, f x ≥ k := fun x hx => hf x (.tail _ hx)
    have h2 := ih f k (a * f hd) htl
    have h3 : a * k ≤ a * f hd := Nat.mul_le_mul_left _ hhd
    have h4 : a * k * k ^ tl.length ≤ a * f hd * k ^ tl.length :=
      Nat.mul_le_mul_right _ h3
    have h5 : a * k * k ^ tl.length = a * k ^ (tl.length + 1) := by
      rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm k (k ^ tl.length)]
    omega

/-- The search space is bounded below by the minimum fiber size raised to N. -/
theorem searchSpace_lower (G : CubeGraph)
    (hmin : ∀ s ∈ allStars G, s.fiberSize ≥ k)
    (hlen : (allStars G).length = n) :
    searchSpace G ≥ k ^ n := by
  unfold searchSpace
  rw [← hlen]
  have := foldl_mul_ge (allStars G) Star.fiberSize k 1 hmin
  simp at this
  exact this

end CubeGraph
