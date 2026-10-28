import OAI.AlgebraicTopology.Cohomology.Singular.CubicalTriangulation
import OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegeneracyOperators
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
import Mathlib.LinearAlgebra.StdBasis

/-! # Cubical Degenerate -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.CubicalDegenerate

noncomputable section

/-!
# Coordinate-degenerate cubes give genuine degenerate simplices

If a cube ignores the kth direction in a permutation, its two consecutive
triangulation vertices at that step coincide. More precisely, merging those
two barycentric weights and reinserting a zero changes only that ignored
coordinate. This proves factorization through the actual simplicial degeneracy
operator, not merely a vanishing determinant or an abstract degeneracy label.
-/

open _root_.CategoryTheory Opposite
open OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegeneracyOperators
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex BigOperators Simplicial ContDiff

variable {n m : ℕ}

/-- Merge two consecutive barycentric weights, then reinsert zero in the second slot. -/
def collapseBarycentricMap (k : Fin (n + 1)) :
    (Fin (n + 2) → ℝ) →L[ℝ] (Fin (n + 2) → ℝ) :=
  (Smooth.simplexLinearMap k.succ.succAbove).comp (Smooth.simplexLinearMap k.predAbove)

/-- The collapse is the ambient extension of an actual degeneracy followed by a face. -/
theorem collapseBarycentricMap_simplex (k : Fin (n + 1))
    (w : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    collapseBarycentricMap k w =
      (Convexity.StdSimplex.map k.succ.succAbove (Convexity.StdSimplex.map k.predAbove w) :
        Fin (n + 2) → ℝ) := by
  change Smooth.simplexLinearMap k.succ.succAbove (Smooth.simplexLinearMap k.predAbove w) = _
  rw [Smooth.simplexLinearMap_weights, Smooth.simplexLinearMap_weights]

/-- On a basis vector the collapse just moves its index through the two finite maps. -/
theorem collapseBarycentricMap_single (k : Fin (n + 1)) (j : Fin (n + 2)) :
    collapseBarycentricMap k (Pi.single j (1 : ℝ)) =
      Pi.single (k.succ.succAbove (k.predAbove j)) 1 := by
  change FunOnFinite.linearMap ℝ ℝ k.succ.succAbove
    (FunOnFinite.linearMap ℝ ℝ k.predAbove (Pi.single j (1 : ℝ))) = _
  rw [FunOnFinite.linearMap_piSingle, FunOnFinite.linearMap_piSingle]

/-- All coordinates except the kth permuted direction are unchanged by the collapse. -/
theorem cubeSimplex_collapse_coordinate (σ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) (a : Fin (n + 1)) (ha : a ≠ σ k)
    (w : Fin (n + 2) → ℝ) :
    CubicalTriangulation.cubeSimplexLinearMap σ (collapseBarycentricMap k w) a =
      CubicalTriangulation.cubeSimplexLinearMap σ w a := by
  let L : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj a).comp
      ((CubicalTriangulation.cubeSimplexLinearMap σ).toLinearMap.comp (collapseBarycentricMap k).toLinearMap)
  let R : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj a).comp (CubicalTriangulation.cubeSimplexLinearMap σ).toLinearMap
  have hLR : L = R := by
    apply (Pi.basisFun ℝ (Fin (n + 2))).ext
    intro j
    rw [Pi.basisFun_apply]
    change CubicalTriangulation.cubeSimplexLinearMap σ (collapseBarycentricMap k (Pi.single j 1)) a =
      CubicalTriangulation.cubeSimplexLinearMap σ (Pi.single j 1) a
    rw [collapseBarycentricMap_single, CubicalTriangulation.cubeSimplexLinearMap_vertex,
      CubicalTriangulation.cubeSimplexLinearMap_vertex]
    by_cases hj : j = k.succ
    · subst j
      simp only [Fin.predAbove_succ_self, Fin.succAbove_succ_self,
        Fin.val_castSucc, Fin.val_succ]
      have hr : (σ.symm a).val ≠ k.val := by
        intro h
        apply ha
        have he : σ.symm a = k := Fin.ext h
        simpa using congrArg σ he
      have hh : (σ.symm a).val < k.val ↔ (σ.symm a).val < k.val + 1 := by omega
      simp only [hh]
    · rw [Fin.succ_succAbove_predAbove hj]
  exact LinearMap.congr_fun hLR w

/-- The collapsed affine image differs by an update of only the kth permuted coordinate. -/
theorem cubeSimplex_collapse_eq_update (σ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) (w : Fin (n + 2) → ℝ) :
    CubicalTriangulation.cubeSimplexLinearMap σ (collapseBarycentricMap k w) =
      Function.update (CubicalTriangulation.cubeSimplexLinearMap σ w) (σ k)
        (CubicalTriangulation.cubeSimplexLinearMap σ (collapseBarycentricMap k w) (σ k)) := by
  funext a
  by_cases ha : a = σ k
  · subst a
    simp
  · rw [Function.update_of_ne ha]
    exact cubeSimplex_collapse_coordinate σ k a ha w

/-- A cube independent of the changed coordinate is unchanged by barycentric collapse. -/
theorem triangulatedCube_collapse
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m)
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1))
    (h : DeRham.Comparison.CubicalDegeneracyOperators.IgnoresCoordinate cube (σ k)) (w : Fin (n + 2) → ℝ) :
    cube (CubicalTriangulation.cubeSimplexLinearMap σ (collapseBarycentricMap k w)) =
      cube (CubicalTriangulation.cubeSimplexLinearMap σ w) := by
  rw [cubeSimplex_collapse_eq_update]
  exact h _ _

/-- An actual smooth triangulation simplex factors through a genuine simplicial degeneracy. -/
theorem triangulatedCubeSmoothSimplex_degeneracy
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m)
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1))
    (h : DeRham.Comparison.CubicalDegeneracyOperators.IgnoresCoordinate cube (σ k)) :
    (Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.σ k
        ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.δ k.succ
          (CubicalTriangulation.triangulatedCubeSmoothSimplex cube σ)) =
      CubicalTriangulation.triangulatedCubeSmoothSimplex cube σ := by
  apply Subtype.ext
  apply ((TopCat.of (Fin m → ℝ)).toSSetObjEquiv (op ⦋n + 1⦌)).injective
  apply ContinuousMap.ext
  intro w
  change cube (CubicalTriangulation.cubeSimplexLinearMap σ
      (Convexity.StdSimplex.map k.succ.succAbove (Convexity.StdSimplex.map k.predAbove w))) =
    cube (CubicalTriangulation.cubeSimplexLinearMap σ w)
  rw [← collapseBarycentricMap_simplex]
  exact triangulatedCube_collapse cube σ k h w

/-- Every permutation simplex of a coordinate-degenerate cube is actually degenerate
in the smooth singular simplicial set. -/
theorem triangulatedCubeSmoothSimplex_mem_degenerate
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m)
    (hc : DeRham.Comparison.CubicalDegeneracyOperators.IsDegenerateCube cube) (σ : Equiv.Perm (Fin (n + 1))) :
    CubicalTriangulation.triangulatedCubeSmoothSimplex cube σ ∈
      (Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.degenerate (n + 1) := by
  obtain ⟨i, hi⟩ := hc
  have h : DeRham.Comparison.CubicalDegeneracyOperators.IgnoresCoordinate cube (σ (σ.symm i)) := by simpa using hi
  have he := triangulatedCubeSmoothSimplex_degeneracy cube σ (σ.symm i) h
  rw [← he]
  exact SSet.σ_mem_degenerate _ _ _

end

end OAI.AlgebraicTopology.Cohomology.Singular.CubicalDegenerate
