import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.CycleClass.Geometric.BarycentricMesh
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Order.Interval.Finset.Fin

/-! # Barycentric Simplex -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex.Cycles

noncomputable section

/-!
# Actual barycentric subdivision maps of topological simplices

A nonempty face has its genuine arithmetic-mean barycenter. A nested flag of
faces gives a continuous simplex map by affine interpolation of those
barycenters. Full flags associated with vertex permutations give the usual
geometric cells of barycentric subdivision.

This module constructs the geometric maps only; no boundary identity,
subdivision chain homotopy, or excision theorem is assumed.
-/

open scoped BigOperators Classical OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The arithmetic-mean point of a nonempty face of the standard simplex. -/
def faceBarycenter (s : Finset ι) (hs : s.Nonempty) : Convexity.StdSimplex ℝ ι := by
  classical
  refine Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates (fun i => if i ∈ s then (s.card : ℝ)⁻¹ else 0) ?_ ?_
  · intro i
    split_ifs <;> positivity
  · have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs.card_pos)
    simp [hcard]

@[simp]
theorem faceBarycenter_apply (s : Finset ι) (hs : s.Nonempty) (i : ι) :
    faceBarycenter s hs i = if i ∈ s then (s.card : ℝ)⁻¹ else 0 := by
  classical
  rfl

/-- The explicit coordinates agree with mathlib's affine centroid. -/
theorem faceBarycenter_eq_centroid [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty) :
    (faceBarycenter s hs : ι → ℝ) = s.centroid ℝ (fun i => Pi.single i (1 : ℝ)) := by
  rw [BarycentricMesh.centroid_eq_inv_card_sum s hs]
  funext i
  rw [faceBarycenter_apply]
  simp [Finset.sum_apply, Pi.single_apply]

/-- Affine interpolation in barycentric coordinates extends to an actual
linear map on the ambient coordinate spaces. -/
def simplexVertexLinearMap (v : κ → Convexity.StdSimplex ℝ ι) : (κ → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  ∑ k, (LinearMap.proj (R := ℝ) k).smulRight (v k : ι → ℝ)

omit [Fintype ι] in
@[simp]
theorem simplexVertexLinearMap_apply (v : κ → Convexity.StdSimplex ℝ ι)
    (x : κ → ℝ) (i : ι) :
    simplexVertexLinearMap v x i = ∑ k, x k * v k i := by
  simp [simplexVertexLinearMap]

omit [Fintype ι] in
/-- The ambient extension is the explicit weighted sum of its vertices. -/
theorem simplexVertexLinearMap_eq_sum (v : κ → Convexity.StdSimplex ℝ ι) (x : κ → ℝ) :
    simplexVertexLinearMap v x = ∑ k, x k • (v k : ι → ℝ) := by
  funext i
  simp [simplexVertexLinearMap_apply, Finset.sum_apply]

/-- The ambient extension is, in particular, an affine map. -/
def simplexVertexAffineMap (v : κ → Convexity.StdSimplex ℝ ι) : (κ → ℝ) →ᵃ[ℝ] (ι → ℝ) :=
  (simplexVertexLinearMap v).toAffineMap

/-- Barycentric interpolation is simplex-valued. -/
theorem simplexVertexLinearMap_mem (v : κ → Convexity.StdSimplex ℝ ι)
    (x : Convexity.StdSimplex ℝ κ) :
    (∀ i, 0 ≤ simplexVertexLinearMap v x i) ∧ ∑ i, simplexVertexLinearMap v x i = 1 := by
  constructor
  · intro i
    rw [simplexVertexLinearMap_apply]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (Convexity.StdSimplex.weights_nonneg (w := x) k) (Convexity.StdSimplex.weights_nonneg (w := v k) i)
  · simp only [simplexVertexLinearMap_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, Convexity.StdSimplex.total_of_fintype, mul_one]

omit [Fintype ι] in
/-- The interpolation map is continuous in the ordinary simplex topology. -/
theorem continuous_simplexVertexLinearMap (v : κ → Convexity.StdSimplex ℝ ι) :
    Continuous (simplexVertexLinearMap v) := by
  apply continuous_pi
  intro i
  simp only [simplexVertexLinearMap_apply]
  fun_prop

/-- The genuine continuous map of simplices specified by its vertex images. -/
def simplexVertexMap (v : κ → Convexity.StdSimplex ℝ ι) : C(Convexity.StdSimplex ℝ κ, Convexity.StdSimplex ℝ ι) where
  toFun x := Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates (simplexVertexLinearMap v x)
    (simplexVertexLinearMap_mem v x).1 (simplexVertexLinearMap_mem v x).2
  continuous_toFun := by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous_iff.mpr
    simpa [Function.comp_def, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates] using
      (continuous_simplexVertexLinearMap v).comp
        (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ κ).continuous

@[simp]
theorem simplexVertexMap_apply (v : κ → Convexity.StdSimplex ℝ ι)
    (x : Convexity.StdSimplex ℝ κ) (i : ι) :
    simplexVertexMap v x i = ∑ k, x k * v k i := by
  simp [simplexVertexMap, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates, simplexVertexLinearMap_apply]

/-- The constructed continuous map is the restriction of the displayed
ambient affine map, not an abstract map with assumed affine properties. -/
theorem simplexVertexMap_eq_affine (v : κ → Convexity.StdSimplex ℝ ι)
    (x : Convexity.StdSimplex ℝ κ) :
    (simplexVertexMap v x : ι → ℝ) = simplexVertexAffineMap v x := by
  funext i
  simp [simplexVertexMap, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates,
    simplexVertexAffineMap]

@[simp]
theorem simplexVertexMap_vertex [DecidableEq κ] (v : κ → Convexity.StdSimplex ℝ ι) (k : κ) :
    simplexVertexMap v (Convexity.StdSimplex.single k) = v k := by
  apply Convexity.StdSimplex.ext
  ext i
  simp [simplexVertexMap_apply, Convexity.StdSimplex.single, Finsupp.single_apply]

/-- Every interpolated point lies in the actual convex hull of the vertex images. -/
theorem simplexVertexMap_mem_convexHull (v : κ → Convexity.StdSimplex ℝ ι)
    (x : Convexity.StdSimplex ℝ κ) :
    (simplexVertexMap v x : ι → ℝ) ∈
      convexHull ℝ (Set.range fun k => (v k : ι → ℝ)) := by
  change simplexVertexLinearMap v x ∈ _
  rw [simplexVertexLinearMap_eq_sum]
  exact (convex_convexHull ℝ _).sum_mem
    (fun k _ => Convexity.StdSimplex.weights_nonneg (w := x) k) (Convexity.StdSimplex.total_of_fintype x)
    (fun k _ => subset_convexHull ℝ _ (Set.mem_range_self k))

/-- Ordered nested nonempty faces, allowing repeated faces for degenerate cells. -/
structure BarycentricFlag (ι : Type*) (m : ℕ) where
  face : Fin (m + 1) → Finset ι
  nonempty : ∀ j, (face j).Nonempty
  monotone : Monotone face

namespace BarycentricFlag

variable {m : ℕ}

/-- The actual geometric simplex corresponding to a face flag. -/
def toContinuousMap (F : BarycentricFlag ι m) :
    C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ ι) :=
  simplexVertexMap (fun j => faceBarycenter (F.face j) (F.nonempty j))

@[simp]
theorem toContinuousMap_vertex (F : BarycentricFlag ι m) (j : Fin (m + 1)) :
    F.toContinuousMap (Convexity.StdSimplex.single j) = faceBarycenter (F.face j) (F.nonempty j) :=
  simplexVertexMap_vertex _ _

@[simp]
theorem toContinuousMap_apply (F : BarycentricFlag ι m)
    (x : Convexity.StdSimplex ℝ (Fin (m + 1))) (i : ι) :
    F.toContinuousMap x i =
      ∑ j, x j * (if i ∈ F.face j then ((F.face j).card : ℝ)⁻¹ else 0) := by
  classical
  simp [BarycentricFlag.toContinuousMap]

/-- The geometric flag simplex lies in the convex hull of its genuine centroids. -/
theorem toContinuousMap_mem_convexHull [DecidableEq ι] (F : BarycentricFlag ι m)
    (x : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    (F.toContinuousMap x : ι → ℝ) ∈ convexHull ℝ
      (Set.range fun j => (F.face j).centroid ℝ (fun i => Pi.single i (1 : ℝ))) := by
  have h := simplexVertexMap_mem_convexHull
    (fun j => faceBarycenter (F.face j) (F.nonempty j)) x
  simpa only [BarycentricFlag.toContinuousMap, faceBarycenter_eq_centroid] using h

/-- A flag cell in the standard `n`-simplex has mesh at most `n/(n+1)`.
The bound follows from the proved face-centroid estimate, not an axiom about subdivision. -/
theorem toContinuousMap_dist_le {n : ℕ} (F : BarycentricFlag (Fin (n + 1)) m)
    (x y : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    dist (F.toContinuousMap x) (F.toContinuousMap y) ≤ (n : ℝ) / (n + 1) := by
  have hchain (j k : Fin (m + 1)) : F.face j ⊆ F.face k ∨ F.face k ⊆ F.face j := by
    rcases le_total j k with h | h
    · exact Or.inl (F.monotone h)
    · exact Or.inr (F.monotone h)
  have hD (i j : Fin (n + 1)) :
      dist (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ)
        (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ) ≤ 1 :=
    by
      apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).2
      intro k
      by_cases hi : i = k <;> by_cases hj : j = k <;>
        simp [hi, hj, Real.dist_eq]
  have h := BarycentricMesh.dist_convexHull_centroids_le_dimension_factor
    (fun i : Fin (n + 1) => Pi.single i (1 : ℝ)) F.face F.nonempty hchain 1 hD
    (F.toContinuousMap_mem_convexHull x) (F.toContinuousMap_mem_convexHull y)
  change dist (F.toContinuousMap x : Fin (n + 1) → ℝ)
    (F.toContinuousMap y : Fin (n + 1) → ℝ) ≤ _
  simpa only [mul_one] using h

end BarycentricFlag

/-- The full nested flag obtained by successively inserting permuted vertices. -/
def permutationBarycentricFlag {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    BarycentricFlag (Fin (n + 1)) n where
  face j := (Finset.Iic j).map σ.toEmbedding
  nonempty j := ⟨σ j, Finset.mem_map.mpr ⟨j, Finset.mem_Iic.mpr le_rfl, rfl⟩⟩
  monotone := by
    intro j k hjk a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    exact Finset.mem_map.mpr ⟨b, Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hb).trans hjk), rfl⟩

@[simp]
theorem permutationBarycentricFlag_card {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (j : Fin (n + 1)) : ((permutationBarycentricFlag σ).face j).card = j.val + 1 := by
  simp [permutationBarycentricFlag]

/-- A standard barycentric subdivision cell, as an actual continuous self-map
of the topological standard simplex. -/
def barycentricSubdivisionMap {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  (permutationBarycentricFlag σ).toContinuousMap

/-- The vertices of the cell are the successive genuine face barycenters. -/
@[simp]
theorem barycentricSubdivisionMap_vertex {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (j : Fin (n + 1)) :
    barycentricSubdivisionMap σ (Convexity.StdSimplex.single j) =
      faceBarycenter ((Finset.Iic j).map σ.toEmbedding)
        ⟨σ j, Finset.mem_map.mpr ⟨j, Finset.mem_Iic.mpr le_rfl, rfl⟩⟩ :=
  (permutationBarycentricFlag σ).toContinuousMap_vertex j

/-- The one-step mesh estimate for every actual subdivision cell. -/
theorem barycentricSubdivisionMap_dist_le {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (x y : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    dist (barycentricSubdivisionMap σ x) (barycentricSubdivisionMap σ y) ≤
      (n : ℝ) / (n + 1) :=
  (permutationBarycentricFlag σ).toContinuousMap_dist_le x y

/-- Subdivision of an individual genuine continuous singular simplex. -/
def subdividedSingularSimplex {X : Type*} [TopologicalSpace X] {n : ℕ}
    (f : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) (σ : Equiv.Perm (Fin (n + 1))) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) :=
  f.comp (barycentricSubdivisionMap σ)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex.Cycles
