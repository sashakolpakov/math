import StickKnots.Geometry

/-!
# A typed polygonal core for the unsliced wall-complement argument

This file is an intentionally unimported prototype.  It replaces the numerical
placeholder for a chamber space by an actual space of labelled polygonal
configurations in `ℝ³`, actual determinant/cross-product wall functions, and a
finite-edge embedding certificate.

The point of using the unsliced configuration space is that its dimension is
`3 * N`, still low enough for the refined real-algebraic component estimate to
give the headline `N^(3N+o(N))` bound.  No Stiefel normalization, affine slice,
or connectedness theorem for `GL⁺(3, ℝ)` is needed for that asymptotic result.
-/

open Set
open scoped Topology

namespace StickKnots

/-- A labelled `N`-vertex configuration in `ℝ³`. -/
abbrev Config (N : ℕ) := Fin N → Vec3

namespace Config

variable {N : ℕ}

/-- The raw configuration viewed through mathlib's polygon wrapper. -/
def toPolygon (p : Config N) : Polygon Vec3 N := ⟨p⟩

@[simp]
theorem toPolygon_apply (p : Config N) (i : Fin N) : p.toPolygon i = p i := rfl

/-- The cyclic successor of an edge/vertex index. -/
abbrev next (i : Fin N) : Fin N := finRotate N i

/-- Directed vector of the edge beginning at `i`. -/
def edgeVec (p : Config N) (i : Fin N) : Vec3 := p (next i) - p i

/-- The affine parametrization of the edge beginning at `i`. -/
def edgePoint (p : Config N) (i : Fin N) (t : ℝ) : Vec3 :=
  p i + t • p.edgeVec i

@[simp]
theorem edgePoint_zero (p : Config N) (i : Fin N) : p.edgePoint i 0 = p i := by
  simp [edgePoint]

@[simp]
theorem edgePoint_one (p : Config N) (i : Fin N) : p.edgePoint i 1 = p (next i) := by
  simp [edgePoint, edgeVec]

/-- The edge parametrization agrees with `Polygon.edgePath`. -/
theorem edgePoint_eq_polygon_edgePath (p : Config N) (i : Fin N) (t : ℝ) :
    p.edgePoint i t = p.toPolygon.edgePath ℝ i t := by
  simp [edgePoint, edgeVec, Polygon.edgePath, AffineMap.lineMap_apply, add_comm]

/-- Two indexed edges are combinatorially nonincident. -/
def Nonincident (i j : Fin N) : Prop :=
  i ≠ j ∧ next i ≠ j ∧ next j ≠ i

/-- The cubic determinant wall for a pair of directed edges. -/
def detWall (p : Config N) (i j : Fin N) : ℝ :=
  det3 (p.edgeVec i) (p.edgeVec j) (p j - p i)

/-- The quartic wall at a vertex, applied to its two consecutive edges. -/
def adjacentWall (p : Config N) (i : Fin N) : ℝ :=
  crossSq (p.edgeVec i) (p.edgeVec (next i))

/-- Complement of all adjacent quartic walls. -/
def AdjacentWallFree (p : Config N) : Prop :=
  ∀ i, p.adjacentWall i ≠ 0

/-- Complement of all cubic walls belonging to nonincident edge pairs. -/
def NonincidentWallFree (p : Config N) : Prop :=
  ∀ i j, Nonincident i j → p.detWall i j ≠ 0

/-- The enlarged algebraic wall complement used by the unsliced argument. -/
def WallFree (p : Config N) : Prop :=
  p.AdjacentWallFree ∧ p.NonincidentWallFree

/-- The wall-free locus as an actual topological subspace. -/
def wallFreeSet (N : ℕ) : Set (Config N) := {p | p.WallFree}

/-- Configurations in the enlarged wall complement. -/
abbrev WallFreeSpace (N : ℕ) := ↥(wallFreeSet N)

/-! ### The walls as genuine multivariate polynomials -/

noncomputable section

/-- A coordinate variable consists of a vertex label and one of three spatial
coordinates. -/
abbrev CoordinateIndex (N : ℕ) := Fin N × Fin 3

/-- Polynomial ring on the `3 * N` vertex coordinates. -/
abbrev WallPolynomial (N : ℕ) := MvPolynomial (CoordinateIndex N) ℝ

/-- The variable for coordinate `k` of vertex `i`. -/
def vertexCoordinatePolynomial (i : Fin N) (k : Fin 3) : WallPolynomial N :=
  MvPolynomial.X (i, k)

/-- Coordinate `k` of the directed edge beginning at `i`. -/
def edgeCoordinatePolynomial (i : Fin N) (k : Fin 3) : WallPolynomial N :=
  vertexCoordinatePolynomial (next i) k - vertexCoordinatePolynomial i k

/-- Cubic scalar-triple-product wall as a genuine multivariate polynomial. -/
def detWallPolynomial (i j : Fin N) : WallPolynomial N :=
  edgeCoordinatePolynomial i 0 *
      (edgeCoordinatePolynomial j 1 *
          (vertexCoordinatePolynomial j 2 - vertexCoordinatePolynomial i 2) -
        edgeCoordinatePolynomial j 2 *
          (vertexCoordinatePolynomial j 1 - vertexCoordinatePolynomial i 1)) -
    edgeCoordinatePolynomial i 1 *
      (edgeCoordinatePolynomial j 0 *
          (vertexCoordinatePolynomial j 2 - vertexCoordinatePolynomial i 2) -
        edgeCoordinatePolynomial j 2 *
          (vertexCoordinatePolynomial j 0 - vertexCoordinatePolynomial i 0)) +
    edgeCoordinatePolynomial i 2 *
      (edgeCoordinatePolynomial j 0 *
          (vertexCoordinatePolynomial j 1 - vertexCoordinatePolynomial i 1) -
        edgeCoordinatePolynomial j 1 *
          (vertexCoordinatePolynomial j 0 - vertexCoordinatePolynomial i 0))

/-- One coordinate of the cross product of consecutive edge vectors. -/
def crossCoordinatePolynomial (i : Fin N) : Fin 3 → WallPolynomial N :=
  ![edgeCoordinatePolynomial i 1 * edgeCoordinatePolynomial (next i) 2 -
      edgeCoordinatePolynomial i 2 * edgeCoordinatePolynomial (next i) 1,
    edgeCoordinatePolynomial i 2 * edgeCoordinatePolynomial (next i) 0 -
      edgeCoordinatePolynomial i 0 * edgeCoordinatePolynomial (next i) 2,
    edgeCoordinatePolynomial i 0 * edgeCoordinatePolynomial (next i) 1 -
      edgeCoordinatePolynomial i 1 * edgeCoordinatePolynomial (next i) 0]

/-- Quartic adjacent-edge wall as a genuine multivariate polynomial. -/
def adjacentWallPolynomial (i : Fin N) : WallPolynomial N :=
  (crossCoordinatePolynomial i 0) ^ 2 +
    (crossCoordinatePolynomial i 1) ^ 2 +
    (crossCoordinatePolynomial i 2) ^ 2

/-- A deliberately redundant polynomial index type.  The left summand holds
the `N` adjacent walls.  The right summand has `N²` slots; irrelevant edge
pairs receive the nonvanishing constant polynomial `1`.  This avoids any
combinatorial cardinality placeholder without changing the asymptotic bound. -/
abbrev WallIndex (N : ℕ) := Fin N ⊕ (Fin N × Fin N)

def indexedWallPolynomial (w : WallIndex N) : WallPolynomial N := by
  classical
  exact match w with
    | Sum.inl i => adjacentWallPolynomial i
    | Sum.inr ij =>
        if Nonincident ij.1 ij.2 then detWallPolynomial ij.1 ij.2 else 1

/-- A configuration as an assignment of values to the polynomial variables. -/
def coordinateAssignment (p : Config N) : CoordinateIndex N → ℝ :=
  fun ik => p ik.1 ik.2

@[simp]
theorem eval_vertexCoordinatePolynomial (p : Config N) (i : Fin N) (k : Fin 3) :
    MvPolynomial.eval p.coordinateAssignment (vertexCoordinatePolynomial i k) = p i k := by
  simp [coordinateAssignment, vertexCoordinatePolynomial]

@[simp]
theorem eval_edgeCoordinatePolynomial (p : Config N) (i : Fin N) (k : Fin 3) :
    MvPolynomial.eval p.coordinateAssignment (edgeCoordinatePolynomial i k) =
      p.edgeVec i k := by
  simp [edgeCoordinatePolynomial, edgeVec]

@[simp]
theorem eval_detWallPolynomial (p : Config N) (i j : Fin N) :
    MvPolynomial.eval p.coordinateAssignment (detWallPolynomial i j) = p.detWall i j := by
  simp [detWallPolynomial, detWall, det3]

@[simp]
theorem eval_crossCoordinatePolynomial (p : Config N) (i : Fin N) (k : Fin 3) :
    MvPolynomial.eval p.coordinateAssignment (crossCoordinatePolynomial i k) =
      cross3 (p.edgeVec i) (p.edgeVec (next i)) k := by
  fin_cases k <;> simp [crossCoordinatePolynomial, cross3]

@[simp]
theorem eval_adjacentWallPolynomial (p : Config N) (i : Fin N) :
    MvPolynomial.eval p.coordinateAssignment (adjacentWallPolynomial i) =
      p.adjacentWall i := by
  simp [adjacentWallPolynomial, adjacentWall, crossSq]

theorem totalDegree_vertexCoordinatePolynomial (i : Fin N) (k : Fin 3) :
    (vertexCoordinatePolynomial i k).totalDegree = 1 := by
  simp [vertexCoordinatePolynomial]

theorem totalDegree_edgeCoordinatePolynomial_le (i : Fin N) (k : Fin 3) :
    (edgeCoordinatePolynomial i k).totalDegree ≤ 1 := by
  exact (MvPolynomial.totalDegree_sub _ _).trans (by simp [vertexCoordinatePolynomial])

private theorem totalDegree_mul_le_two
    {a b : WallPolynomial N} (ha : a.totalDegree ≤ 1) (hb : b.totalDegree ≤ 1) :
    (a * b).totalDegree ≤ 2 :=
  (MvPolynomial.totalDegree_mul _ _).trans <| by omega

private theorem totalDegree_crossCoordinatePolynomial_le (i : Fin N) (k : Fin 3) :
    (crossCoordinatePolynomial i k).totalDegree ≤ 2 := by
  fin_cases k <;>
    simp only [crossCoordinatePolynomial]
  all_goals
    exact (MvPolynomial.totalDegree_sub _ _).trans <|
      max_le
        (totalDegree_mul_le_two
          (totalDegree_edgeCoordinatePolynomial_le _ _)
          (totalDegree_edgeCoordinatePolynomial_le _ _))
        (totalDegree_mul_le_two
          (totalDegree_edgeCoordinatePolynomial_le _ _)
          (totalDegree_edgeCoordinatePolynomial_le _ _))

private theorem totalDegree_crossSquare_le_four (i : Fin N) (k : Fin 3) :
    ((crossCoordinatePolynomial i k) ^ 2).totalDegree ≤ 4 :=
  (MvPolynomial.totalDegree_pow _ 2).trans <| by
    have hk := totalDegree_crossCoordinatePolynomial_le i k
    omega

/-- Every adjacent wall in the explicit family has degree at most four. -/
theorem totalDegree_adjacentWallPolynomial_le (i : Fin N) :
    (adjacentWallPolynomial i).totalDegree ≤ 4 := by
  unfold adjacentWallPolynomial
  exact (MvPolynomial.totalDegree_add _ _).trans <| max_le
    ((MvPolynomial.totalDegree_add _ _).trans <| max_le
      (totalDegree_crossSquare_le_four i 0)
      (totalDegree_crossSquare_le_four i 1))
    (totalDegree_crossSquare_le_four i 2)

private theorem totalDegree_coordinateDifference_le (i j : Fin N) (k : Fin 3) :
    (vertexCoordinatePolynomial j k - vertexCoordinatePolynomial i k).totalDegree ≤ 1 := by
  exact (MvPolynomial.totalDegree_sub _ _).trans (by simp [vertexCoordinatePolynomial])

private theorem totalDegree_detBracket_le_two
    (j i : Fin N) (a b : Fin 3) :
    (edgeCoordinatePolynomial j a *
          (vertexCoordinatePolynomial j b - vertexCoordinatePolynomial i b) -
        edgeCoordinatePolynomial j b *
          (vertexCoordinatePolynomial j a - vertexCoordinatePolynomial i a)).totalDegree ≤ 2 := by
  exact (MvPolynomial.totalDegree_sub _ _).trans <| max_le
    (totalDegree_mul_le_two
      (totalDegree_edgeCoordinatePolynomial_le _ _)
      (totalDegree_coordinateDifference_le _ _ _))
    (totalDegree_mul_le_two
      (totalDegree_edgeCoordinatePolynomial_le _ _)
      (totalDegree_coordinateDifference_le _ _ _))

private theorem totalDegree_edge_mul_bracket_le_three
    (i j : Fin N) (k a b : Fin 3) :
    (edgeCoordinatePolynomial i k *
      (edgeCoordinatePolynomial j a *
          (vertexCoordinatePolynomial j b - vertexCoordinatePolynomial i b) -
        edgeCoordinatePolynomial j b *
          (vertexCoordinatePolynomial j a - vertexCoordinatePolynomial i a))).totalDegree ≤ 3 :=
  (MvPolynomial.totalDegree_mul _ _).trans <| by
    have h₁ := totalDegree_edgeCoordinatePolynomial_le i k
    have h₂ := totalDegree_detBracket_le_two j i a b
    omega

/-- Every determinant wall in the explicit family has degree at most three. -/
theorem totalDegree_detWallPolynomial_le (i j : Fin N) :
    (detWallPolynomial i j).totalDegree ≤ 3 := by
  unfold detWallPolynomial
  exact (MvPolynomial.totalDegree_add _ _).trans <| max_le
    ((MvPolynomial.totalDegree_sub _ _).trans <| max_le
      (totalDegree_edge_mul_bracket_le_three i j 0 1 2)
      (totalDegree_edge_mul_bracket_le_three i j 1 0 2))
    (totalDegree_edge_mul_bracket_le_three i j 2 0 1)

/-- Every slot of the redundant wall family has degree at most four. -/
theorem totalDegree_indexedWallPolynomial_le (w : WallIndex N) :
    (indexedWallPolynomial w).totalDegree ≤ 4 := by
  rcases w with i | ⟨i, j⟩
  · exact (totalDegree_adjacentWallPolynomial_le i)
  · simp only [indexedWallPolynomial]
    split
    · exact (totalDegree_detWallPolynomial_le i j).trans (by omega)
    · simp

theorem card_wallIndex : Fintype.card (WallIndex N) = N + N * N := by
  simp [WallIndex]

/-- `WallFree` is exactly the complement of the zero sets of the explicit
degree-at-most-four polynomial family. -/
theorem wallFree_iff_forall_indexedWallPolynomial_ne_zero (p : Config N) :
    p.WallFree ↔
      ∀ w : WallIndex N,
        MvPolynomial.eval p.coordinateAssignment (indexedWallPolynomial w) ≠ 0 := by
  constructor
  · rintro ⟨hadj, hnon⟩ (i | ⟨i, j⟩)
    · simpa [indexedWallPolynomial] using hadj i
    · simp only [indexedWallPolynomial]
      split_ifs with hij
      · simpa using hnon i j hij
      · simp
  · intro h
    constructor
    · intro i
      simpa [indexedWallPolynomial] using h (Sum.inl i)
    · intro i j hij
      simpa [indexedWallPolynomial, hij] using h (Sum.inr (i, j))

end

theorem edgeVec_ne_zero_of_adjacentWall_ne_zero {p : Config N} {i : Fin N}
    (h : p.adjacentWall i ≠ 0) : p.edgeVec i ≠ 0 := by
  intro hi
  apply h
  simp [adjacentWall, hi, crossSq, cross3]

theorem next_edgeVec_ne_zero_of_adjacentWall_ne_zero {p : Config N} {i : Fin N}
    (h : p.adjacentWall i ≠ 0) : p.edgeVec (next i) ≠ 0 := by
  intro hi
  apply h
  rw [adjacentWall, hi]
  simp [crossSq, cross3]

/-- A noncollapsed straight edge has an injective affine parametrization. -/
theorem edgePoint_injective {p : Config N} {i : Fin N} (h : p.edgeVec i ≠ 0) :
    Function.Injective (p.edgePoint i) := by
  intro t s hts
  apply smul_left_injective ℝ h
  apply add_left_cancel (a := p i)
  simpa [edgePoint] using hts

/-- Finite-edge certificate that the cyclic polygon is embedded.

The adjacent clause is deliberately parametrized: it states that consecutive
edges meet only at their prescribed endpoint.  The nonincident clause rules
out every meeting of combinatorially disjoint edges. -/
structure Embedded (p : Config N) : Prop where
  edge_injective : ∀ i, Function.Injective (p.edgePoint i)
  adjacent_only_common : ∀ i t s,
    p.edgePoint i t = p.edgePoint (next i) s → t = 1 ∧ s = 0
  nonincident_disjoint : ∀ i j, Nonincident i j →
    ∀ t s, p.edgePoint i t ≠ p.edgePoint j s

theorem adjacent_only_common_of_wall_free {p : Config N}
    (h : p.AdjacentWallFree) (i : Fin N) (t s : ℝ)
    (hts : p.edgePoint i t = p.edgePoint (next i) s) :
    t = 1 ∧ s = 0 := by
  have hwall := h i
  have ht : t = 1 := by
    by_contra ht
    apply hwall
    apply adjacent_improper_intersection_implies_crossSq_wall
      (p i) (p (next i)) (p (next (next i))) t s ht
    simpa [edgePoint, edgeVec] using hts
  have hnext : p.edgeVec (next i) ≠ 0 :=
    next_edgeVec_ne_zero_of_adjacentWall_ne_zero hwall
  refine ⟨ht, ?_⟩
  apply edgePoint_injective hnext
  calc
    p.edgePoint (next i) s = p.edgePoint i t := hts.symm
    _ = p (next i) := by simp [ht]
    _ = p.edgePoint (next i) 0 := (edgePoint_zero _ _).symm

theorem nonincident_disjoint_of_wall_free {p : Config N}
    (h : p.NonincidentWallFree) (i j : Fin N) (hij : Nonincident i j)
    (t s : ℝ) : p.edgePoint i t ≠ p.edgePoint j s := by
  intro hmeet
  apply h i j hij
  apply segment_intersection_implies_det_wall
    (p i) (p (next i)) (p j) (p (next j)) t s
  simpa [edgePoint, edgeVec] using hmeet

/-- The explicit polynomial walls really do certify an embedded cyclic
polygon; no topology or knot theory is hidden in this implication. -/
theorem wallFree_embedded {p : Config N} (h : p.WallFree) : p.Embedded where
  edge_injective i := edgePoint_injective <|
    edgeVec_ne_zero_of_adjacentWall_ne_zero (h.1 i)
  adjacent_only_common i t s hts :=
    adjacent_only_common_of_wall_free h.1 i t s hts
  nonincident_disjoint i j hij t s :=
    nonincident_disjoint_of_wall_free h.2 i j hij t s

/-- The parameterized edge used above is exactly mathlib's segment-valued
`Polygon.edgeSet`. -/
theorem polygon_edgeSet_eq_image_edgePoint (p : Config N) (i : Fin N) :
    p.toPolygon.edgeSet ℝ i = p.edgePoint i '' Icc 0 1 := by
  rw [Polygon.edgeSet_eq_image_edgePath]
  apply Set.image_congr
  intro t _
  exact (edgePoint_eq_polygon_edgePath p i t).symm

/-- Wall freedom implies mathlib's standard nondegenerate-edge predicate. -/
theorem wallFree_hasNondegenerateEdges {p : Config N} (h : p.WallFree) :
    p.toPolygon.HasNondegenerateEdges := by
  intro i hi
  change p i = p (next i) at hi
  apply edgeVec_ne_zero_of_adjacentWall_ne_zero (h.1 i)
  simp [edgeVec, hi]

/-- Mathlib's actual segment sets for nonincident edges are disjoint. -/
theorem wallFree_nonincident_edgeSet_disjoint {p : Config N} (h : p.WallFree)
    (i j : Fin N) (hij : Nonincident i j) :
    Disjoint (p.toPolygon.edgeSet ℝ i) (p.toPolygon.edgeSet ℝ j) := by
  rw [polygon_edgeSet_eq_image_edgePoint, polygon_edgeSet_eq_image_edgePoint]
  refine Set.disjoint_left.2 ?_
  rintro x ⟨t, _, rfl⟩ ⟨s, _, hmeet⟩
  exact nonincident_disjoint_of_wall_free h.2 i j hij t s hmeet.symm

/-- Consecutive mathlib segment sets intersect exactly in their common cyclic
vertex. -/
theorem wallFree_adjacent_edgeSet_inter {p : Config N} (h : p.WallFree) (i : Fin N) :
    p.toPolygon.edgeSet ℝ i ∩ p.toPolygon.edgeSet ℝ (next i) = {p (next i)} := by
  rw [polygon_edgeSet_eq_image_edgePoint, polygon_edgeSet_eq_image_edgePoint]
  ext x
  constructor
  · rintro ⟨⟨t, _, rfl⟩, ⟨s, _, hmeet⟩⟩
    have hparam := adjacent_only_common_of_wall_free h.1 i t s hmeet.symm
    rw [hparam.1]
    simp
  · intro hx
    rw [mem_singleton_iff] at hx
    subst x
    constructor
    · exact ⟨1, by norm_num, by simp⟩
    · exact ⟨0, by norm_num, by simp⟩

theorem continuous_edgeVec (i : Fin N) : Continuous fun p : Config N => p.edgeVec i := by
  unfold edgeVec
  fun_prop

theorem continuous_detWall (i j : Fin N) : Continuous fun p : Config N => p.detWall i j := by
  unfold detWall det3 edgeVec
  fun_prop

theorem continuous_adjacentWall (i : Fin N) :
    Continuous fun p : Config N => p.adjacentWall i := by
  unfold adjacentWall crossSq cross3 edgeVec
  fun_prop

private theorem isOpen_adjacentWall_ne (i : Fin N) :
    IsOpen {p : Config N | p.adjacentWall i ≠ 0} :=
  isOpen_ne_fun (continuous_adjacentWall i) continuous_const

private theorem isOpen_nonincidentWall_condition (i j : Fin N) :
    IsOpen {p : Config N | Nonincident i j → p.detWall i j ≠ 0} := by
  by_cases hij : Nonincident i j
  · simpa [hij] using isOpen_ne_fun (continuous_detWall i j) continuous_const
  · simp [hij]

/-- The enlarged wall complement is an open subset of the Euclidean
configuration space. -/
theorem isOpen_wallFreeSet : IsOpen (wallFreeSet N) := by
  rw [show wallFreeSet N =
      (⋂ i, {p : Config N | p.adjacentWall i ≠ 0}) ∩
        ⋂ i, ⋂ j, {p : Config N | Nonincident i j → p.detWall i j ≠ 0} by
    ext p
    simp [wallFreeSet, WallFree, AdjacentWallFree, NonincidentWallFree]]
  exact (isOpen_iInter_of_finite isOpen_adjacentWall_ne).inter <|
    isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun j => isOpen_nonincidentWall_condition i j

instance locallyPathConnectedSpace_wallFreeSpace :
    LocallyPathConnectedSpace (WallFreeSpace N) :=
  isOpen_wallFreeSet.locallyPathConnectedSpace

/-- Polygonal-isotopy classes internal to the wall-free locus. -/
abbrev PolygonalIsotopyClasses (N : ℕ) := ZerothHomotopy (WallFreeSpace N)

/-- On this open Euclidean locus, connected components and path components
coincide. -/
noncomputable def connectedComponentsEquivPolygonalIsotopyClasses :
    ConnectedComponents (WallFreeSpace N) ≃ PolygonalIsotopyClasses N :=
  connectedComponentsEquivZerothHomotopy

theorem joined_iff_same_connectedComponent (p q : WallFreeSpace N) :
    Joined p q ↔ connectedComponent p = connectedComponent q := by
  rw [connectedComponent_eq_iff_joined]

end Config

end StickKnots
