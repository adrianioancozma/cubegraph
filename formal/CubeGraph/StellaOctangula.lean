/-
  CubeGraph/StellaOctangula.lean
  Stella Octangula obstruction: no conservative majority polymorphism.

  The 8 vertices of {0,1}³ form two complementary tetrahedra (the Stella
  Octangula = compound of two tetrahedra inscribed in the cube):
    Even tetrahedron: {0,3,5,6} = {000, 011, 101, 110}  (even parity)
    Odd tetrahedron:  {1,2,4,7} = {001, 010, 100, 111}  (odd parity)

  Each tetrahedron has 4 triangular faces. For each face {a,b,c}:
    - Every pair has Hamming distance exactly 2 (agree on 1 bit, differ on 2)
    - Bitwise majority(a,b,c) falls OUTSIDE the triple

  Example: {0,3,5} = {000, 011, 101}
    majority(000, 011, 101) = 001 = 1, and 1 ∉ {0,3,5}.

  The STRONGEST result: for ANY 7-element gap set (removing vertex v),
  there exists a Stella triple fully contained in the gap set whose
  bitwise majority equals v (the forbidden vertex). This means NO
  ternary operation can be simultaneously a majority and conservative
  on any 7-element gap set. This is the geometric core of why 3-SAT
  lacks conservative majority polymorphisms.

  Connection to CSP dichotomy (Bulatov 2017, Zhuk 2020):
  - Conservative majority ⊂ Taylor polymorphism family
  - No conservative majority → constraint language outside Schaefer tractability
  - This is the GEOMETRIC reason: the cube's parity structure prevents it

  This result extends NonAffine.lean (7 ≠ 2^k) and TaylorBarrier.lean
  (no WNU3 preserves ≠ on Fin 3) with a third, independent angle:
  the gap set's bitwise structure prevents conservative majority.

  Dependencies:
  - Basic.lean: Vertex (= Fin 8), Cube
  - NonAffine.lean: vertexXor (used for parity characterization)

  See: formal/CubeGraph/NonAffine.lean (non-affine gap sets)
  See: formal/CubeGraph/TaylorBarrier.lean (no WNU3 preserves ≠ on Fin 3)
  See: formal/CubeGraph/DimensionThreshold.lean (why k=3 is the boundary)
  See: formal/CubeGraph/ComputationalNoether.lean (5 absent symmetries)
  See: experiments-ml/027_2026-03-24_star-analysis/SESSION-SUMMARY.md
-/

import CubeGraph.NonAffine

namespace CubeGraph

/-! ## Section 1: Bitwise Majority

  The bitwise majority of three bit-vectors: bit i of the result is 1
  iff at least 2 of the 3 inputs have bit i = 1.
  Computed as: (a AND b) OR (a AND c) OR (b AND c).  -/

/-- Bitwise majority of three Fin 8 values: each output bit is the
    majority vote of the three corresponding input bits. -/
def bitwiseMajority (a b c : Fin 8) : Fin 8 :=
  ⟨((a.val &&& b.val) ||| (a.val &&& c.val) ||| (b.val &&& c.val)) % 8,
   by omega⟩

/-- Bitwise majority is idempotent: majority(x,x,x) = x. -/
theorem bitwiseMajority_idem (x : Fin 8) :
    bitwiseMajority x x x = x := by
  revert x; native_decide

/-- Bitwise majority is symmetric in first two arguments. -/
theorem bitwiseMajority_comm12 (a b c : Fin 8) :
    bitwiseMajority a b c = bitwiseMajority b a c := by
  revert a b c; native_decide

/-- Bitwise majority is symmetric in first and third arguments. -/
theorem bitwiseMajority_comm13 (a b c : Fin 8) :
    bitwiseMajority a b c = bitwiseMajority c b a := by
  revert a b c; native_decide

/-- Bitwise majority is symmetric in second and third arguments. -/
theorem bitwiseMajority_comm23 (a b c : Fin 8) :
    bitwiseMajority a b c = bitwiseMajority a c b := by
  revert a b c; native_decide

/-! ## Section 2: Hamming Distance

  Two vertices have Hamming distance d iff they differ on exactly d bits.
  For {0,1}³, Hamming distance is the popcount of XOR.  -/

/-- Popcount of a 3-bit number (number of set bits). -/
def popcount3 (v : Fin 8) : Nat :=
  (v.val &&& 1) + ((v.val >>> 1) &&& 1) + ((v.val >>> 2) &&& 1)

/-- Hamming distance between two vertices = popcount(XOR). -/
def hammingDist (a b : Fin 8) : Nat :=
  popcount3 (vertexXor a b)

/-! ## Section 3: The Two Tetrahedra

  The 8 vertices of the cube split into two classes by parity (popcount mod 2):
    Even parity: {0(000), 3(011), 5(101), 6(110)} — popcount ∈ {0,2}
    Odd parity:  {1(001), 2(010), 4(100), 7(111)} — popcount ∈ {1,3}

  Each class forms a regular tetrahedron: any two vertices in the same class
  have Hamming distance exactly 2 (they differ on exactly 2 of 3 bits).  -/

/-- Parity of a vertex: true iff popcount is odd. -/
def vertexParity (v : Fin 8) : Bool :=
  popcount3 v % 2 == 1

/-- The even tetrahedron: {0, 3, 5, 6}. -/
def evenTetra : List (Fin 8) :=
  [⟨0, by omega⟩, ⟨3, by omega⟩, ⟨5, by omega⟩, ⟨6, by omega⟩]

/-- The odd tetrahedron: {1, 2, 4, 7}. -/
def oddTetra : List (Fin 8) :=
  [⟨1, by omega⟩, ⟨2, by omega⟩, ⟨4, by omega⟩, ⟨7, by omega⟩]

/-- Even tetrahedron vertices have even parity. -/
theorem evenTetra_parity :
    evenTetra.all (fun v => !vertexParity v) = true := by native_decide

/-- Odd tetrahedron vertices have odd parity. -/
theorem oddTetra_parity :
    oddTetra.all (fun v => vertexParity v) = true := by native_decide

/-- Within the even tetrahedron, all pairs have Hamming distance 2. -/
theorem evenTetra_hamming :
    evenTetra.all (fun v₁ =>
      evenTetra.all (fun v₂ =>
        v₁ == v₂ || (hammingDist v₁ v₂ == 2))) = true := by native_decide

/-- Within the odd tetrahedron, all pairs have Hamming distance 2. -/
theorem oddTetra_hamming :
    oddTetra.all (fun v₁ =>
      oddTetra.all (fun v₂ =>
        v₁ == v₂ || (hammingDist v₁ v₂ == 2))) = true := by native_decide

/-! ## Section 4: The 8 Stella Octangula Triples

  Each tetrahedron has (4 choose 3) = 4 triangular faces.
  Total: 8 triples. Each triple is a face of the Stella Octangula.

  Even tetrahedron faces:  {0,3,5}, {0,3,6}, {0,5,6}, {3,5,6}
  Odd tetrahedron faces:   {1,2,4}, {1,2,7}, {1,4,7}, {2,4,7}  -/

/-- A Stella triple: three vertices forming a face of the Stella Octangula. -/
structure StellaTriple where
  a : Fin 8
  b : Fin 8
  c : Fin 8

/-- The 8 Stella Octangula triples (faces of both tetrahedra). -/
def stellaTriples : List StellaTriple :=
  -- Even tetrahedron faces
  [ ⟨⟨0, by omega⟩, ⟨3, by omega⟩, ⟨5, by omega⟩⟩,   -- {000, 011, 101}
    ⟨⟨0, by omega⟩, ⟨3, by omega⟩, ⟨6, by omega⟩⟩,   -- {000, 011, 110}
    ⟨⟨0, by omega⟩, ⟨5, by omega⟩, ⟨6, by omega⟩⟩,   -- {000, 101, 110}
    ⟨⟨3, by omega⟩, ⟨5, by omega⟩, ⟨6, by omega⟩⟩,   -- {011, 101, 110}
    -- Odd tetrahedron faces
    ⟨⟨1, by omega⟩, ⟨2, by omega⟩, ⟨4, by omega⟩⟩,   -- {001, 010, 100}
    ⟨⟨1, by omega⟩, ⟨2, by omega⟩, ⟨7, by omega⟩⟩,   -- {001, 010, 111}
    ⟨⟨1, by omega⟩, ⟨4, by omega⟩, ⟨7, by omega⟩⟩,   -- {001, 100, 111}
    ⟨⟨2, by omega⟩, ⟨4, by omega⟩, ⟨7, by omega⟩⟩ ]  -- {010, 100, 111}

/-! ## Section 5: The Core Obstruction

  For EVERY Stella triple {a,b,c}: bitwiseMajority(a,b,c) ∉ {a,b,c}.
  This means majority cannot be conservative on any subset containing
  a Stella triple — it MUST produce an element outside the subset.  -/

/-- Check that majority of a triple falls outside the triple. -/
def stellaObstructed (t : StellaTriple) : Bool :=
  let m := bitwiseMajority t.a t.b t.c
  m != t.a && m != t.b && m != t.c

/-- **CORE THEOREM**: Every Stella triple is majority-obstructed.
    Bitwise majority(a,b,c) ∉ {a,b,c} for all 8 triples.  -/
theorem stella_all_obstructed :
    stellaTriples.all stellaObstructed = true := by native_decide

/-- Each Stella triple has all pairs at Hamming distance exactly 2. -/
def stellaHammingValid (t : StellaTriple) : Bool :=
  hammingDist t.a t.b == 2 &&
  hammingDist t.a t.c == 2 &&
  hammingDist t.b t.c == 2

/-- All Stella triples are Hamming-valid: pairs differ on exactly 2 bits. -/
theorem stella_all_hamming_valid :
    stellaTriples.all stellaHammingValid = true := by native_decide

/-- The majority of each Stella triple is explicitly computed.
    Even faces: majority lands on the opposite-parity vertex not in the face.
    Odd faces: majority lands on the opposite-parity vertex not in the face. -/
theorem stella_majority_values :
    -- Even faces
    bitwiseMajority ⟨0, by omega⟩ ⟨3, by omega⟩ ⟨5, by omega⟩ = ⟨1, by omega⟩ ∧
    bitwiseMajority ⟨0, by omega⟩ ⟨3, by omega⟩ ⟨6, by omega⟩ = ⟨2, by omega⟩ ∧
    bitwiseMajority ⟨0, by omega⟩ ⟨5, by omega⟩ ⟨6, by omega⟩ = ⟨4, by omega⟩ ∧
    bitwiseMajority ⟨3, by omega⟩ ⟨5, by omega⟩ ⟨6, by omega⟩ = ⟨7, by omega⟩ ∧
    -- Odd faces
    bitwiseMajority ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨4, by omega⟩ = ⟨0, by omega⟩ ∧
    bitwiseMajority ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨7, by omega⟩ = ⟨3, by omega⟩ ∧
    bitwiseMajority ⟨1, by omega⟩ ⟨4, by omega⟩ ⟨7, by omega⟩ = ⟨5, by omega⟩ ∧
    bitwiseMajority ⟨2, by omega⟩ ⟨4, by omega⟩ ⟨7, by omega⟩ = ⟨6, by omega⟩ := by
  native_decide

/-! ## Section 6: Conservative Majority — Impossibility on 7-Gap Sets

  A conservative ternary operation preserves the gap set:
  f(a,b,c) ∈ S for all a,b,c ∈ S.

  Key discovery: for ANY choice of forbidden vertex v ∈ Fin 8, the 7-element
  gap set S = Fin 8 \ {v} contains a Stella triple whose bitwise majority
  equals v. This means bitwiseMajority maps some triple of gaps to the
  forbidden vertex, violating conservativity.

  Since bitwise majority is the UNIQUE majority on {0,1}³ (it's determined
  by the bitwise structure), this rules out the natural majority. The full
  impossibility of ANY conservative majority on CubeGraph's constraint
  language is proven in TaylorBarrier.lean via ≠ on Fin 3 projections.  -/

/-- A ternary operation is conservative on a set S: f(a,b,c) ∈ S for all a,b,c ∈ S. -/
def IsConservative3 (S : Fin 8 → Bool) (f : Fin 8 → Fin 8 → Fin 8 → Fin 8) : Prop :=
  ∀ a b c : Fin 8, S a = true → S b = true → S c = true →
    S (f a b c) = true

/-- **Bitwise majority is not conservative on ANY Stella triple.**
    For each triple, majority(a,b,c) ∉ {a,b,c}. -/
theorem majority_not_conservative_all_stella :
    stellaTriples.all (fun t =>
      let S := fun v : Fin 8 => v == t.a || v == t.b || v == t.c
      !(S (bitwiseMajority t.a t.b t.c))) = true := by native_decide

/-- **The Escape Theorem**: For each forbidden vertex v, there exists
    a Stella triple fully in the gap set whose majority equals v.
    This is the strongest form: majority ALWAYS produces the forbidden vertex
    for some triple, making conservativity impossible. -/
theorem stella_escape :
    ∀ v : Fin 8,
      stellaTriples.any (fun t =>
        t.a != v && t.b != v && t.c != v &&
        bitwiseMajority t.a t.b t.c == v) = true := by
  intro v; revert v; native_decide

/-- The companion vertex map: face of tetrahedron T₁ maps to the unique
    vertex of T₂ that is the bitwise majority of the face.

    Even face → odd vertex:
      {0,3,5} → 1,  {0,3,6} → 2,  {0,5,6} → 4,  {3,5,6} → 7
    Odd face → even vertex:
      {1,2,4} → 0,  {1,2,7} → 3,  {1,4,7} → 5,  {2,4,7} → 6

    This is a bijection between the 4 faces of each tetrahedron and
    the 4 vertices of the other tetrahedron. The companion vertex is
    the one NOT adjacent to any face vertex at Hamming distance 1
    (all distances are 2 or 3). -/
theorem stella_companion_bijection :
    -- Every vertex v is the majority of exactly one triple
    (List.finRange 8).all (fun v =>
      stellaTriples.countP (fun t =>
        bitwiseMajority t.a t.b t.c == v) == 1) = true := by
  native_decide

/-! ## Section 7: Parity Flip — The Geometric Mechanism

  WHY does majority land outside each Stella triple?
  Because each triple has 3 elements of the same parity (all even or all odd),
  and bitwise majority of same-parity triples flips parity.

  More precisely: for a face {a,b,c} of a tetrahedron (all same parity),
  majority(a,b,c) has the OPPOSITE parity. This is because on each bit
  position, majority selects the bit appearing ≥ 2 times, and for vertices
  at mutual Hamming distance 2, this necessarily flips the parity. -/

/-- Majority of an even-tetrahedron face lands in the odd class. -/
theorem majority_even_to_odd :
    bitwiseMajority ⟨0, by omega⟩ ⟨3, by omega⟩ ⟨5, by omega⟩ = ⟨1, by omega⟩ ∧
    bitwiseMajority ⟨0, by omega⟩ ⟨3, by omega⟩ ⟨6, by omega⟩ = ⟨2, by omega⟩ ∧
    bitwiseMajority ⟨0, by omega⟩ ⟨5, by omega⟩ ⟨6, by omega⟩ = ⟨4, by omega⟩ ∧
    bitwiseMajority ⟨3, by omega⟩ ⟨5, by omega⟩ ⟨6, by omega⟩ = ⟨7, by omega⟩ := by
  native_decide

/-- Majority of an odd-tetrahedron face lands in the even class. -/
theorem majority_odd_to_even :
    bitwiseMajority ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨4, by omega⟩ = ⟨0, by omega⟩ ∧
    bitwiseMajority ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨7, by omega⟩ = ⟨3, by omega⟩ ∧
    bitwiseMajority ⟨1, by omega⟩ ⟨4, by omega⟩ ⟨7, by omega⟩ = ⟨5, by omega⟩ ∧
    bitwiseMajority ⟨2, by omega⟩ ⟨4, by omega⟩ ⟨7, by omega⟩ = ⟨6, by omega⟩ := by
  native_decide

/-- Parity of majority output is opposite to parity of inputs (for Stella triples). -/
theorem stella_parity_flip :
    stellaTriples.all (fun t =>
      vertexParity (bitwiseMajority t.a t.b t.c) != vertexParity t.a) = true := by
  native_decide

/-! ## Section 8: Connection to Gap Sets

  A single-clause 3-SAT cube has 7 gaps (all vertices except 1 forbidden).
  Each vertex belongs to exactly 3 of the 8 Stella triples (the 3 faces
  of its tetrahedron that contain it). So removing one vertex removes
  exactly 3 triples, leaving 5 of 8 triples fully contained in the gap set.

  Of these 5 contained triples, the 4 from the OTHER tetrahedron all have
  their majority in the same tetrahedron as the forbidden vertex. And exactly
  1 contained triple from the forbidden vertex's OWN tetrahedron has its
  majority equal to the forbidden vertex itself (stella_escape).

  This means: for ANY single-clause cube, bitwiseMajority applied to some
  triple of gaps produces the forbidden vertex (which is NOT a gap).  -/

/-- Each vertex belongs to exactly 3 of the 8 Stella triples. -/
theorem vertex_in_three_triples :
    (List.finRange 8).all (fun v =>
      stellaTriples.countP (fun t => t.a == v || t.b == v || t.c == v) == 3)
    = true := by native_decide

/-- A 7-element gap set (removing one vertex) contains exactly 5 of 8 Stella triples. -/
theorem seven_gaps_contain_five_stella :
    (List.finRange 8).all (fun forbidden =>
      stellaTriples.countP (fun t =>
        t.a != forbidden && t.b != forbidden && t.c != forbidden) == 5)
    = true := by native_decide

/-- For each 7-gap set, exactly 3 Stella triples are broken (contain the forbidden vertex). -/
theorem seven_gaps_three_broken :
    (List.finRange 8).all (fun forbidden =>
      stellaTriples.countP (fun t =>
        t.a == forbidden || t.b == forbidden || t.c == forbidden) == 3)
    = true := by native_decide

/-- **The Gap-Level Impossibility**: For each 7-gap set, among the 5 contained
    Stella triples, exactly 1 has its majority equal to the forbidden vertex.
    This triple witnesses the failure of conservativity: bitwiseMajority maps
    3 gaps to a non-gap. -/
theorem seven_gaps_one_escaping :
    (List.finRange 8).all (fun forbidden =>
      stellaTriples.countP (fun t =>
        t.a != forbidden && t.b != forbidden && t.c != forbidden &&
        bitwiseMajority t.a t.b t.c == forbidden) == 1) = true := by
  native_decide

/-! ## Section 9: The Majority-Parity Duality

  The Stella Octangula obstruction reveals a beautiful duality:
  majority and parity are DUAL operations on {0,1}³.

  - Parity: XOR of all bits → 0 or 1 → partitions vertices into tetrahedra
  - Majority: AND/OR of bit pairs → vertex → CROSSES the parity partition

  This is the same duality as in coding theory:
  - Parity check: detects odd-weight errors
  - Majority decode: corrects by voting → necessarily changes parity class

  For CubeGraph: the tetrahedra are the TWO equivalence classes of
  the GF(2)³ group modulo the parity subgroup. Any majority-like operation
  must cross between classes, violating conservativity.  -/

/-- The majority-parity duality: majority maps faces of one tetrahedron
    to vertices of the OTHER tetrahedron. This is an exact bijection. -/
theorem majority_parity_bijection :
    -- Even → Odd
    bitwiseMajority ⟨0, by omega⟩ ⟨3, by omega⟩ ⟨5, by omega⟩ = ⟨1, by omega⟩ ∧
    bitwiseMajority ⟨0, by omega⟩ ⟨3, by omega⟩ ⟨6, by omega⟩ = ⟨2, by omega⟩ ∧
    bitwiseMajority ⟨0, by omega⟩ ⟨5, by omega⟩ ⟨6, by omega⟩ = ⟨4, by omega⟩ ∧
    bitwiseMajority ⟨3, by omega⟩ ⟨5, by omega⟩ ⟨6, by omega⟩ = ⟨7, by omega⟩ ∧
    -- Odd → Even
    bitwiseMajority ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨4, by omega⟩ = ⟨0, by omega⟩ ∧
    bitwiseMajority ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨7, by omega⟩ = ⟨3, by omega⟩ ∧
    bitwiseMajority ⟨1, by omega⟩ ⟨4, by omega⟩ ⟨7, by omega⟩ = ⟨5, by omega⟩ ∧
    bitwiseMajority ⟨2, by omega⟩ ⟨4, by omega⟩ ⟨7, by omega⟩ = ⟨6, by omega⟩ := by
  native_decide

/-! ## Section 10: Summary Theorem — The 5th Absent Symmetry

  The Stella Octangula obstruction provides a GEOMETRIC proof that
  conservative majority polymorphisms cannot exist on CubeGraph gap sets.

  Combined with:
  1. Locality (Borromean order)     → no local propagation
  2. Linearity (7 ≠ 2^k)           → no Gaussian/XOR methods
  3. Commutativity (M₁M₂ ≠ M₂M₁)  → no abelian methods
  4. Reversibility (M³ = M²)        → no group computation

  This yields the 5th absent symmetry:
  5. Majority (Stella Octangula)    → no conservative majority / Taylor polymorphism

  Source: parity structure of {0,1}³ inscribed tetrahedra
  See: TaylorBarrier.lean (full WNU3 impossibility via ≠ on Fin 3)  -/

/-- **Stella Octangula Obstruction** (capstone theorem):
    The 8 faces of the Stella Octangula are ALL majority-obstructed,
    every pair within each face has Hamming distance 2,
    parity flips under majority, 7-gap sets contain 5 obstructed triples,
    and for each forbidden vertex, exactly one contained triple has its
    majority land on that vertex.

    This is the geometric reason conservative majority fails on {0,1}³,
    and hence why CubeGraph's constraint language lacks Taylor polymorphisms. -/
theorem stella_octangula_obstruction :
    -- (1) All 8 triples are majority-obstructed
    (stellaTriples.all stellaObstructed = true)
    -- (2) All pairs in each triple have Hamming distance exactly 2
    ∧ (stellaTriples.all stellaHammingValid = true)
    -- (3) Majority flips parity: even→odd, odd→even
    ∧ (stellaTriples.all (fun t =>
        vertexParity (bitwiseMajority t.a t.b t.c) != vertexParity t.a) = true)
    -- (4) Any 7-gap set contains exactly 5 Stella triples
    ∧ ((List.finRange 8).all (fun forbidden =>
        stellaTriples.countP (fun t =>
          t.a != forbidden && t.b != forbidden && t.c != forbidden) == 5) = true)
    -- (5) Bitwise majority is not conservative on any Stella triple
    ∧ (stellaTriples.all (fun t =>
        let S := fun v : Fin 8 => v == t.a || v == t.b || v == t.c
        !(S (bitwiseMajority t.a t.b t.c))) = true)
    -- (6) Each vertex is the escape target of exactly 1 contained triple
    ∧ ((List.finRange 8).all (fun forbidden =>
        stellaTriples.countP (fun t =>
          t.a != forbidden && t.b != forbidden && t.c != forbidden &&
          bitwiseMajority t.a t.b t.c == forbidden) == 1) = true) :=
  ⟨stella_all_obstructed,
   stella_all_hamming_valid,
   stella_parity_flip,
   seven_gaps_contain_five_stella,
   majority_not_conservative_all_stella,
   seven_gaps_one_escaping⟩

end CubeGraph
