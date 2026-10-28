import OAI.AlgebraicTopology.Cohomology.Singular.Smooth
import OAI.AlgebraicTopology.DeRham.Comparison.StokesF
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-! # Cubical Triangulation -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.CubicalTriangulation

noncomputable section

/-!
# Affine simplex parameterizations of a cube

For a permutation of the `n` coordinate directions, the vertices of the
associated cube simplex successively switch on those directions. Its barycentric
parameterization is a globally defined continuous linear map on the ambient
`n+1` barycentric coordinates. This file proves its vertex formula, its landing
in the actual unit cube, and smoothness of composition with actual smooth cubes.

No cancellation of triangulation faces or equivalence of chain complexes is
asserted here. In particular this does not identify unnormalized cubical
homology with singular homology.
-/

open _root_.CategoryTheory Opposite
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex BigOperators Simplicial ContDiff

variable {n m : ℕ}

/-- The ambient linear map for the standard cube simplex belonging to a
permutation. Coordinate `σ(i)` is the tail sum of barycentric weights after i. -/
def cubeSimplexLinearMap (σ : Equiv.Perm (Fin n)) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    ∑ j : Fin (n + 1),
      (if (σ.symm i).val < j.val then (1 : ℝ) else 0) •
        ContinuousLinearMap.proj (R := ℝ) j

/-- The same parameterization viewed as an affine map. -/
def cubeSimplexAffineMap (σ : Equiv.Perm (Fin n)) :
    (Fin (n + 1) → ℝ) →ᵃ[ℝ] (Fin n → ℝ) :=
  (cubeSimplexLinearMap σ).toLinearMap.toAffineMap

/-- Explicit tail-sum coordinate formula. -/
@[simp]
theorem cubeSimplexLinearMap_apply (σ : Equiv.Perm (Fin n))
    (w : Fin (n + 1) → ℝ) (i : Fin n) :
    cubeSimplexLinearMap σ w i =
      ∑ j : Fin (n + 1), if (σ.symm i).val < j.val then w j else 0 := by
  simp [cubeSimplexLinearMap, ContinuousLinearMap.pi_apply]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

/-- The kth vertex has switched on precisely the first k permuted directions. -/
theorem cubeSimplexLinearMap_vertex (σ : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) (i : Fin n) :
    cubeSimplexLinearMap σ (Pi.single k (1 : ℝ)) i =
      if (σ.symm i).val < k.val then 1 else 0 := by
  rw [cubeSimplexLinearMap_apply]
  classical
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hne
    simp [hne]
  · simp

/-- Barycentric points of the standard simplex map into the actual unit cube. -/
theorem cubeSimplexLinearMap_mem_unitCube (σ : Equiv.Perm (Fin n))
    {w : Fin (n + 1) → ℝ} (hw : w ∈ Set.range (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
      (x.weights : Fin (n + 1) → ℝ))) :
    cubeSimplexLinearMap σ w ∈ DeRham.Comparison.StokesF.SingularCubeStokes.unitCube n := by
  rcases hw with ⟨w, rfl⟩
  change (∀ i, 0 ≤ cubeSimplexLinearMap σ w i) ∧
    (∀ i, cubeSimplexLinearMap σ w i ≤ 1)
  constructor
  · intro i
    rw [cubeSimplexLinearMap_apply]
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact w.weights_nonneg j
    · exact le_rfl
  · intro i
    rw [cubeSimplexLinearMap_apply]
    calc
      _ ≤ ∑ j : Fin (n + 1), w j := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs
        · exact le_rfl
        · exact w.weights_nonneg j
      _ = 1 := w.total_of_fintype

/-- The ambient extension is globally smooth, including across simplex faces. -/
theorem cubeSimplexLinearMap_contDiff (σ : Equiv.Perm (Fin n)) :
    ContDiff ℝ ∞ (cubeSimplexLinearMap σ) :=
  (cubeSimplexLinearMap σ).contDiff

/-- The actual continuous map from the standard simplex into the cube subtype. -/
def cubeSimplexMap (σ : Equiv.Perm (Fin n)) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), DeRham.Comparison.StokesF.SingularCubeStokes.unitCube n) where
  toFun w := ⟨cubeSimplexLinearMap σ w, cubeSimplexLinearMap_mem_unitCube σ ⟨w, rfl⟩⟩
  continuous_toFun :=
    ((cubeSimplexLinearMap σ).continuous.comp (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous).subtype_mk _

/-- The simplex in ambient cube coordinates. -/
def cubeSimplexAmbientMap (σ : Equiv.Perm (Fin n)) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), Fin n → ℝ) where
  toFun w := cubeSimplexLinearMap σ w
  continuous_toFun := (cubeSimplexLinearMap σ).continuous.comp (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous

/-- The parameterization satisfies the genuine neighborhood-extension definition
of a smooth singular simplex. -/
theorem isSmoothSimplex_cubeSimplexAmbientMap (σ : Equiv.Perm (Fin n)) :
    Smooth.IsSmoothSimplex (cubeSimplexAmbientMap σ) :=
  ⟨cubeSimplexLinearMap σ, Set.univ, isOpen_univ, Set.subset_univ _,
    (cubeSimplexLinearMap_contDiff σ).contDiffOn, fun _ => rfl⟩

/-- Compose an actual smooth singular cube with one affine simplex parameterization. -/
def triangulatedCubeSimplex (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube n m)
    (σ : Equiv.Perm (Fin n)) : C(Convexity.StdSimplex ℝ (Fin (n + 1)), Fin m → ℝ) where
  toFun w := cube.toFun (cubeSimplexLinearMap σ w)
  continuous_toFun := cube.smooth.continuous.comp
    ((cubeSimplexLinearMap σ).continuous.comp (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous)

/-- Every simplex obtained from an actual smooth cube has a global smooth
extension in barycentric coordinates, hence a smooth neighborhood extension. -/
theorem isSmoothSimplex_triangulatedCubeSimplex
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube n m) (σ : Equiv.Perm (Fin n)) :
    Smooth.IsSmoothSimplex (triangulatedCubeSimplex cube σ) :=
  ⟨cube.toFun ∘ cubeSimplexLinearMap σ, Set.univ, isOpen_univ, Set.subset_univ _,
    (cube.smooth.comp (cubeSimplexLinearMap_contDiff σ)).contDiffOn, fun _ => rfl⟩

/-- The parameterized simplex as an element of the actual smooth singular
simplicial subcomplex, ready for use in its chain module. -/
def triangulatedCubeSmoothSimplex (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube n m)
    (σ : Equiv.Perm (Fin n)) :
    (Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet _⦋n⦌ := by
  refine ⟨((TopCat.of (Fin m → ℝ)).toSSetObjEquiv (op ⦋n⦌)).symm
    (triangulatedCubeSimplex cube σ), ?_⟩
  change Smooth.IsSmoothSimplex ((TopCat.of (Fin m → ℝ)).toSSetObjEquiv (op ⦋n⦌)
    (((TopCat.of (Fin m → ℝ)).toSSetObjEquiv (op ⦋n⦌)).symm
      (triangulatedCubeSimplex cube σ)))
  simpa only [Equiv.apply_symm_apply] using isSmoothSimplex_triangulatedCubeSimplex cube σ

/-- The resulting genuine singular simplex has the prescribed continuous map. -/
@[simp]
theorem triangulatedCubeSmoothSimplex_continuousMap
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube n m) (σ : Equiv.Perm (Fin n)) :
    (TopCat.of (Fin m → ℝ)).toSSetObjEquiv (op ⦋n⦌)
      (triangulatedCubeSmoothSimplex cube σ).val = triangulatedCubeSimplex cube σ := by
  simp [triangulatedCubeSmoothSimplex]

end

end OAI.AlgebraicTopology.Cohomology.Singular.CubicalTriangulation
