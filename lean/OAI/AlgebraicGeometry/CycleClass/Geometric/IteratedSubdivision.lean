import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex
import OAI.AlgebraicGeometry.CycleClass.Geometric.SingularChainSupport
import Mathlib.Tactic.Ring

/-! # Iterated Subdivision -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.IteratedSubdivision.Cycles

noncomputable section

/-!
# Iterated actual barycentric maps and geometric smallness

We iterate the constructed barycentric affine maps themselves. The mesh estimate
comes from the centroids of the current vertices; it does not assume that a
single barycentric map has an unproved Lipschitz constant. Finite support and a
Lebesgue number then make every iterated cell of an actual integral chain small.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory
open scoped BigOperators Simplicial

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

/-- Barycentric affine interpolation respects actual composition. -/
theorem simplexVertexMap_comp (v : κ → Convexity.StdSimplex ℝ ι)
    (w : μ → Convexity.StdSimplex ℝ κ) :
    (BarycentricSimplex.Cycles.simplexVertexMap v).comp (BarycentricSimplex.Cycles.simplexVertexMap w) =
      BarycentricSimplex.Cycles.simplexVertexMap (fun j => BarycentricSimplex.Cycles.simplexVertexMap v (w j)) := by
  ext x i
  simp only [ContinuousMap.comp_apply, BarycentricSimplex.Cycles.simplexVertexMap_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Interpolation of the original vertices is the identity simplex map. -/
theorem simplexVertexMap_vertices [DecidableEq ι] :
    BarycentricSimplex.Cycles.simplexVertexMap (fun i : ι => Convexity.StdSimplex.single i) =
      ContinuousMap.id (Convexity.StdSimplex ℝ ι) := by
  ext x i
  simp [BarycentricSimplex.Cycles.simplexVertexMap_apply, Convexity.StdSimplex.single, Finsupp.single_apply]

/-- An affine barycentric map sends the barycenter of a face to the actual
arithmetic centroid of its vertex images. -/
theorem simplexVertexMap_faceBarycenter (v : κ → Convexity.StdSimplex ℝ ι)
    (s : Finset κ) (hs : s.Nonempty) :
    (BarycentricSimplex.Cycles.simplexVertexMap v (BarycentricSimplex.Cycles.faceBarycenter s hs) : ι → ℝ) =
      s.centroid ℝ (fun j => (v j : ι → ℝ)) := by
  classical
  rw [BarycentricMesh.centroid_eq_inv_card_sum s hs]
  funext i
  simp [BarycentricSimplex.Cycles.simplexVertexMap_apply, BarycentricSimplex.Cycles.faceBarycenter_apply,
    Finset.sum_apply, Finset.mul_sum, ite_mul]

/-- The mesh factor for an `n`-dimensional simplex. -/
abbrev barycentricMeshFactor (n : ℕ) : ℝ := (n : ℝ) / (n + 1)

theorem barycentricMeshFactor_nonneg (n : ℕ) : 0 ≤ barycentricMeshFactor n := by
  positivity

theorem barycentricMeshFactor_lt_one (n : ℕ) : barycentricMeshFactor n < 1 := by
  apply (div_lt_one (by positivity : (0 : ℝ) < n + 1)).2
  linarith

/-- The actual new vertices obtained by applying one barycentric cell to a
simplex with the specified old vertices. -/
def subdivideSimplexVertices {n : ℕ} (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι)
    (σ : Equiv.Perm (Fin (n + 1))) : Fin (n + 1) → Convexity.StdSimplex ℝ ι :=
  fun j => BarycentricSimplex.Cycles.simplexVertexMap v
    (BarycentricSimplex.Cycles.faceBarycenter ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).face j)
      ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).nonempty j))

/-- This vertex construction is exactly precomposition by the existing
barycentric subdivision map. -/
theorem simplexVertexMap_subdivide {n : ℕ}
    (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι) (σ : Equiv.Perm (Fin (n + 1))) :
    BarycentricSimplex.Cycles.simplexVertexMap (subdivideSimplexVertices v σ) =
      (BarycentricSimplex.Cycles.simplexVertexMap v).comp (BarycentricSimplex.Cycles.barycentricSubdivisionMap σ) := by
  symm
  exact simplexVertexMap_comp v _

/-- One genuine subdivision contracts the current vertex diameter bound. -/
theorem subdivideSimplexVertices_dist_le {n : ℕ}
    (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι) (σ : Equiv.Perm (Fin (n + 1)))
    (D : ℝ) (hD : ∀ i j, dist (v i) (v j) ≤ D) (i j : Fin (n + 1)) :
    dist (subdivideSimplexVertices v σ i) (subdivideSimplexVertices v σ j) ≤
      barycentricMeshFactor n * D := by
  have hchain : (BarycentricSimplex.Cycles.permutationBarycentricFlag σ).face i ⊆
      (BarycentricSimplex.Cycles.permutationBarycentricFlag σ).face j ∨
      (BarycentricSimplex.Cycles.permutationBarycentricFlag σ).face j ⊆ (BarycentricSimplex.Cycles.permutationBarycentricFlag σ).face i := by
    rcases le_total i j with hij | hji
    · exact Or.inl ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).monotone hij)
    · exact Or.inr ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).monotone hji)
  have h := BarycentricMesh.dist_centroid_le_dimension_factor
    (fun k => (v k : ι → ℝ)) _ _
    ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).nonempty i)
    ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).nonempty j) hchain D hD
  rw [← simplexVertexMap_faceBarycenter v _ ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).nonempty i),
    ← simplexVertexMap_faceBarycenter v _ ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).nonempty j)] at h
  simpa only [subdivideSimplexVertices, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.dist_eq_weights] using h

/-- Successive actual barycentric vertex constructions; the head permutation
is the newest precomposition. -/
def iteratedSimplexVertices {n : ℕ} (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι)
    (l : List (Equiv.Perm (Fin (n + 1)))) : Fin (n + 1) → Convexity.StdSimplex ℝ ι :=
  l.foldr (fun σ w => subdivideSimplexVertices w σ) v

/-- The actual affine map of an iterated subdivision cell. -/
def iteratedSimplexMap {n : ℕ} (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι)
    (l : List (Equiv.Perm (Fin (n + 1)))) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), Convexity.StdSimplex ℝ ι) :=
  BarycentricSimplex.Cycles.simplexVertexMap (iteratedSimplexVertices v l)

@[simp]
theorem iteratedSimplexMap_nil {n : ℕ} (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι) :
    iteratedSimplexMap v [] = BarycentricSimplex.Cycles.simplexVertexMap v := rfl

@[simp]
theorem iteratedSimplexMap_cons {n : ℕ} (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι)
    (σ : Equiv.Perm (Fin (n + 1))) (l : List (Equiv.Perm (Fin (n + 1)))) :
    iteratedSimplexMap v (σ :: l) =
      (iteratedSimplexMap v l).comp (BarycentricSimplex.Cycles.barycentricSubdivisionMap σ) :=
  simplexVertexMap_subdivide _ _

/-- The iterated vertex estimate, with the actual initial diameter bound. -/
theorem iteratedSimplexVertices_dist_le {n : ℕ}
    (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι) (D : ℝ)
    (hD : ∀ i j, dist (v i) (v j) ≤ D)
    (l : List (Equiv.Perm (Fin (n + 1)))) (i j : Fin (n + 1)) :
    dist (iteratedSimplexVertices v l i) (iteratedSimplexVertices v l j) ≤
      barycentricMeshFactor n ^ l.length * D := by
  induction l generalizing i j with
  | nil => simpa [iteratedSimplexVertices] using hD i j
  | cons σ l ih =>
      have hprev (a b : Fin (n + 1)) := ih a b
      calc
        dist (iteratedSimplexVertices v (σ :: l) i)
            (iteratedSimplexVertices v (σ :: l) j) ≤
            barycentricMeshFactor n * (barycentricMeshFactor n ^ l.length * D) :=
          subdivideSimplexVertices_dist_le _ σ _ hprev i j
        _ = barycentricMeshFactor n ^ (σ :: l).length * D := by
          simp only [List.length_cons, pow_succ]
          ring

/-- The mesh estimate holds for all points in the actual iterated cell. -/
theorem iteratedSimplexMap_dist_le {n : ℕ}
    (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι) (D : ℝ)
    (hD : ∀ i j, dist (v i) (v j) ≤ D)
    (l : List (Equiv.Perm (Fin (n + 1))))
    (x y : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    dist (iteratedSimplexMap v l x) (iteratedSimplexMap v l y) ≤
      barycentricMeshFactor n ^ l.length * D := by
  have hx := BarycentricSimplex.Cycles.simplexVertexMap_mem_convexHull (iteratedSimplexVertices v l) x
  have hy := BarycentricSimplex.Cycles.simplexVertexMap_mem_convexHull (iteratedSimplexVertices v l) y
  obtain ⟨x', ⟨i, rfl⟩, y', ⟨j, rfl⟩, hxy⟩ := convexHull_exists_dist_ge2 hx hy
  exact hxy.trans (iteratedSimplexVertices_dist_le v D hD l i j)

/-- Actual diameter contraction of the image, relative to the initial vertices. -/
theorem iteratedSimplexMap_diam_le {n : ℕ}
    (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι)
    (l : List (Equiv.Perm (Fin (n + 1)))) :
    Metric.diam (Set.range (iteratedSimplexMap v l)) ≤
      barycentricMeshFactor n ^ l.length * Metric.diam (Set.range v) := by
  apply Metric.diam_le_of_forall_dist_le (mul_nonneg
    (pow_nonneg (barycentricMeshFactor_nonneg n) _) Metric.diam_nonneg)
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact iteratedSimplexMap_dist_le v _
    (fun i j => Metric.dist_le_diam_of_mem (Set.finite_range v).isBounded
      (Set.mem_range_self i) (Set.mem_range_self j)) l x y

/-- The same contraction bound relative to the diameter of the entire initial
affine simplex, rather than only its vertex set. -/
theorem iteratedSimplexMap_diam_le_initial {n : ℕ}
    (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι)
    (l : List (Equiv.Perm (Fin (n + 1)))) :
    Metric.diam (Set.range (iteratedSimplexMap v l)) ≤
      barycentricMeshFactor n ^ l.length * Metric.diam (Set.range (BarycentricSimplex.Cycles.simplexVertexMap v)) := by
  have hsub : Set.range v ⊆ Set.range (BarycentricSimplex.Cycles.simplexVertexMap v) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Convexity.StdSimplex.single i, BarycentricSimplex.Cycles.simplexVertexMap_vertex v i⟩
  have hbdd := (isCompact_range (BarycentricSimplex.Cycles.simplexVertexMap v).continuous).isBounded
  exact (iteratedSimplexMap_diam_le v l).trans (mul_le_mul_of_nonneg_left
    (Metric.diam_mono hsub hbdd) (pow_nonneg (barycentricMeshFactor_nonneg n) _))

/-- Iteration starting with the standard simplex itself. -/
def iteratedSubdivisionMap {n : ℕ} (l : List (Equiv.Perm (Fin (n + 1)))) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  iteratedSimplexMap (fun i => Convexity.StdSimplex.single i) l

@[simp]
theorem iteratedSubdivisionMap_nil {n : ℕ} :
    iteratedSubdivisionMap (n := n) [] = ContinuousMap.id _ :=
  simplexVertexMap_vertices

@[simp]
theorem iteratedSubdivisionMap_cons {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (l : List (Equiv.Perm (Fin (n + 1)))) :
    iteratedSubdivisionMap (σ :: l) =
      (iteratedSubdivisionMap l).comp (BarycentricSimplex.Cycles.barycentricSubdivisionMap σ) :=
  iteratedSimplexMap_cons _ _ _

/-- The uniform mesh bound for every genuine iterated standard cell. -/
theorem iteratedSubdivisionMap_dist_le {n : ℕ}
    (l : List (Equiv.Perm (Fin (n + 1))))
    (x y : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    dist (iteratedSubdivisionMap l x) (iteratedSubdivisionMap l y) ≤
      barycentricMeshFactor n ^ l.length := by
  have hD (i j : Fin (n + 1)) :
      dist (Convexity.StdSimplex.single i : Convexity.StdSimplex ℝ (Fin (n + 1)))
        (Convexity.StdSimplex.single j) ≤ 1 :=
    (Metric.dist_le_diam_of_mem
      (Convexity.StdSimplex.isBounded_range_toFun_comp_weights (Fin (n + 1)))
      ⟨Convexity.StdSimplex.single i, rfl⟩ ⟨Convexity.StdSimplex.single j, rfl⟩).trans
        (Convexity.StdSimplex.diam_range_toFun_comp_weights_subset_closedBall (Fin (n + 1)))
  simpa only [mul_one, iteratedSubdivisionMap] using iteratedSimplexMap_dist_le
    (fun i => Convexity.StdSimplex.single i) 1 hD l x y

/-- A common number of actual barycentric iterations makes every cell of every
simplex in a finite family subordinate to the given open cover. -/
theorem singularSimplices_iteratedSubdivision_small {X : TopCat.{0}} {J : Type}
    (U : J → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i) {n : ℕ}
    (s : Finset C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ N : ℕ, ∀ σ ∈ s, ∀ l : List (Equiv.Perm (Fin (n + 1))),
      l.length = N → ∃ i, Set.range (σ.comp (iteratedSubdivisionMap l)) ⊆ U i := by
  obtain ⟨N, hN⟩ := SmallSimplex.Cycles.singularSimplices_geometric_smallness U hopen hcover s
    (barycentricMeshFactor_lt_one n)
  refine ⟨N, ?_⟩
  intro σ hσ l hl
  apply hN σ hσ n (iteratedSubdivisionMap l)
  intro x y
  simpa only [hl] using iteratedSubdivisionMap_dist_le l x y

/-- In particular, one common number of iterations works on the actual finite
support of every genuine integral singular chain. No mesh assumption remains. -/
theorem singularChain_iteratedSubdivision_small {X : TopCat.{0}} {J : Type}
    (U : J → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i) {n : ℕ}
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    ∃ N : ℕ, ∀ σ ∈ SingularChainSupport.Cycles.singularChainSupport c,
      ∀ l : List (Equiv.Perm (Fin (n + 1))), l.length = N →
      ∃ i, Set.range ((X.toSSetObjEquiv (.op ⦋n⦌) σ).comp
        (iteratedSubdivisionMap l)) ⊆ U i := by
  obtain ⟨N, hN⟩ := SingularChainSupport.Cycles.singularChain_geometric_smallness U hopen hcover c
    (barycentricMeshFactor_lt_one n)
  refine ⟨N, ?_⟩
  intro σ hσ l hl
  apply hN σ hσ n (iteratedSubdivisionMap l)
  intro x y
  simpa only [hl] using iteratedSubdivisionMap_dist_le l x y

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.IteratedSubdivision.Cycles
