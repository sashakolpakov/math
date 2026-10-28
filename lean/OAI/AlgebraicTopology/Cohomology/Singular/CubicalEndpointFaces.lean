import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicTopology.Cohomology.Singular.CubicalFaces
import OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas
import OAI.AlgebraicTopology.DeRham.Comparison.StokesF
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Cubical Endpoint Faces -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.CubicalEndpointFaces

noncomputable section

/-!
# Exact endpoint faces of permutation simplices in a cube

Deleting the first or last simplex vertex factors the entire parameterization
through the corresponding upper or lower cube face. The residual simplex is
indexed by the permutation obtained by deleting the matching coordinate
direction. These are exact equalities of the actual continuous maps.
-/

open _root_.CategoryTheory Opposite
open scoped BigOperators Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

variable {n m : ℕ}

/-- Delete an input position and its image from a finite permutation, retaining
the increasing order on the remaining input and output labels. -/
def eraseCubePermutation (σ : Equiv.Perm (Fin (n + 1))) (p : Fin (n + 1)) :
    Equiv.Perm (Fin n) :=
  (finSuccAboveEquiv p).trans
    ((σ.subtypeEquiv (p := fun a => a ≠ p) (q := fun b => b ≠ σ p)
      (by intro a; simp)).trans (finSuccAboveEquiv (σ p)).symm)

/-- The reduced permutation commutes with insertion of the deleted labels. -/
theorem eraseCubePermutation_succAbove (σ : Equiv.Perm (Fin (n + 1)))
    (p : Fin (n + 1)) (j : Fin n) :
    (σ p).succAbove (eraseCubePermutation σ p j) = σ (p.succAbove j) := by
  have h := congrArg Subtype.val
    ((finSuccAboveEquiv (σ p)).apply_symm_apply
      ⟨σ (p.succAbove j), by
        intro he
        exact p.succAbove_ne j (σ.injective he)⟩)
  exact h

/-- The inverse reduced permutation commutes with the same label insertions. -/
theorem eraseCubePermutation_symm_succAbove (σ : Equiv.Perm (Fin (n + 1)))
    (p : Fin (n + 1)) (j : Fin n) :
    σ.symm ((σ p).succAbove j) = p.succAbove ((eraseCubePermutation σ p).symm j) := by
  apply σ.injective
  have h := eraseCubePermutation_succAbove σ p ((eraseCubePermutation σ p).symm j)
  simpa only [Equiv.apply_symm_apply] using h

/-- A retained coordinate of a simplex face has its original barycentric weight. -/
theorem standardSimplexFace_kept_coordinate (k : Fin (n + 1))
    (w : Convexity.StdSimplex ℝ (Fin n)) (j : Fin n) :
    Convexity.StdSimplex.map k.succAbove w (k.succAbove j) = w j := by
  classical
  change (Convexity.StdSimplex.map k.succAbove w).weights (k.succAbove j) = w.weights j
  rw [Convexity.StdSimplex.weights_map]
  exact Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective w.weights j

/-- All retained cube coordinates on the first simplex face are the coordinates
of the simplex for the reduced permutation. -/
theorem cubeSimplex_firstFace_coordinate (σ : Equiv.Perm (Fin (n + 1)))
    (w : Convexity.StdSimplex ℝ (Fin (n + 1))) (a : Fin n) :
    CubicalTriangulation.cubeSimplexLinearMap σ (Convexity.StdSimplex.map (0 : Fin (n + 2)).succAbove w)
        ((σ 0).succAbove a) =
      CubicalTriangulation.cubeSimplexLinearMap (eraseCubePermutation σ 0) w a := by
  have hface (j : Fin (n + 1)) :
      Convexity.StdSimplex.map Fin.succ w j.succ = w j := by
    simpa only [Fin.succAbove_zero] using standardSimplexFace_kept_coordinate 0 w j
  rw [CubicalTriangulation.cubeSimplexLinearMap_apply, CubicalTriangulation.cubeSimplexLinearMap_apply,
    eraseCubePermutation_symm_succAbove]
  simp only [Fin.succAbove_zero, Fin.val_succ]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.not_lt_zero, ite_false, zero_add, Fin.val_succ,
    Nat.add_lt_add_iff_right, hface]

/-- All retained cube coordinates on the last simplex face are the coordinates
of the simplex for the reduced permutation. -/
theorem cubeSimplex_lastFace_coordinate (σ : Equiv.Perm (Fin (n + 1)))
    (w : Convexity.StdSimplex ℝ (Fin (n + 1))) (a : Fin n) :
    CubicalTriangulation.cubeSimplexLinearMap σ (Convexity.StdSimplex.map (Fin.last (n + 1)).succAbove w)
        ((σ (Fin.last n)).succAbove a) =
      CubicalTriangulation.cubeSimplexLinearMap (eraseCubePermutation σ (Fin.last n)) w a := by
  have hface (j : Fin (n + 1)) :
      Convexity.StdSimplex.map Fin.castSucc w j.castSucc = w j := by
    simpa only [Fin.succAbove_last] using
      standardSimplexFace_kept_coordinate (Fin.last (n + 1)) w j
  have hlast : Convexity.StdSimplex.map Fin.castSucc w (Fin.last (n + 1)) = 0 := by
    simpa only [Fin.succAbove_last] using
      CubicalFaces.standardSimplexFace_omitted_coordinate (Fin.last (n + 1)) w
  rw [CubicalTriangulation.cubeSimplexLinearMap_apply, CubicalTriangulation.cubeSimplexLinearMap_apply,
    eraseCubePermutation_symm_succAbove]
  simp only [Fin.succAbove_last, Fin.val_castSucc]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, hface, hlast,
    ite_self, add_zero]

/-- Exact factorization of the first simplex face through the upper cube face. -/
theorem cubeSimplex_firstFace_factorization (σ : Equiv.Perm (Fin (n + 1)))
    (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    CubicalTriangulation.cubeSimplexLinearMap σ (Convexity.StdSimplex.map (0 : Fin (n + 2)).succAbove w) =
      DeRham.Comparison.StokesF.SingularCubeStokes.faceInclusion (σ 0) 1
        (CubicalTriangulation.cubeSimplexLinearMap (eraseCubePermutation σ 0) w) := by
  apply funext
  intro a
  induction a using Fin.succAboveCases (σ 0) with
  | x =>
      change CubicalTriangulation.cubeSimplexLinearMap σ (Convexity.StdSimplex.map (0 : Fin (n + 2)).succAbove w)
          (σ 0) = Fin.insertNth (α := fun _ => ℝ) (σ 0) 1
          (CubicalTriangulation.cubeSimplexLinearMap (eraseCubePermutation σ 0) w) (σ 0)
      simp only [Fin.insertNth_apply_same]
      exact CubicalFaces.cubeSimplex_firstCoordinate_eq_one σ _ (CubicalFaces.standardSimplexFace_omitted_coordinate 0 w)
  | p j =>
      change CubicalTriangulation.cubeSimplexLinearMap σ (Convexity.StdSimplex.map (0 : Fin (n + 2)).succAbove w)
          ((σ 0).succAbove j) = Fin.insertNth (α := fun _ => ℝ) (σ 0) 1
          (CubicalTriangulation.cubeSimplexLinearMap (eraseCubePermutation σ 0) w) ((σ 0).succAbove j)
      simpa only [Fin.insertNth_apply_succAbove] using cubeSimplex_firstFace_coordinate σ w j

/-- Exact factorization of the last simplex face through the lower cube face. -/
theorem cubeSimplex_lastFace_factorization (σ : Equiv.Perm (Fin (n + 1)))
    (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    CubicalTriangulation.cubeSimplexLinearMap σ (Convexity.StdSimplex.map (Fin.last (n + 1)).succAbove w) =
      DeRham.Comparison.StokesF.SingularCubeStokes.faceInclusion (σ (Fin.last n)) 0
        (CubicalTriangulation.cubeSimplexLinearMap (eraseCubePermutation σ (Fin.last n)) w) := by
  apply funext
  intro a
  induction a using Fin.succAboveCases (σ (Fin.last n)) with
  | x =>
      change CubicalTriangulation.cubeSimplexLinearMap σ (Convexity.StdSimplex.map (Fin.last (n + 1)).succAbove w)
          (σ (Fin.last n)) = Fin.insertNth (α := fun _ => ℝ) (σ (Fin.last n)) 0
          (CubicalTriangulation.cubeSimplexLinearMap (eraseCubePermutation σ (Fin.last n)) w) (σ (Fin.last n))
      simpa only [Fin.insertNth_apply_same, CubicalFaces.cubeSimplex_lastCoordinate] using
        CubicalFaces.standardSimplexFace_omitted_coordinate (Fin.last (n + 1)) w
  | p j =>
      change CubicalTriangulation.cubeSimplexLinearMap σ (Convexity.StdSimplex.map (Fin.last (n + 1)).succAbove w)
          ((σ (Fin.last n)).succAbove j) = Fin.insertNth (α := fun _ => ℝ) (σ (Fin.last n)) 0
          (CubicalTriangulation.cubeSimplexLinearMap (eraseCubePermutation σ (Fin.last n)) w)
            ((σ (Fin.last n)).succAbove j)
      simpa only [Fin.insertNth_apply_succAbove] using cubeSimplex_lastFace_coordinate σ w j

/-- The first face of a triangulated smooth cube is precisely a simplex of its upper cube face. -/
theorem triangulatedCubeSimplex_firstFace
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (CubicalTriangulation.triangulatedCubeSimplex cube σ).comp (ContinuousFormulas.standardSimplexFace (0 : Fin (n + 2))) =
      CubicalTriangulation.triangulatedCubeSimplex (DeRham.Comparison.StokesF.SingularCubeStokes.singularFace cube (σ 0) 1)
        (eraseCubePermutation σ 0) := by
  apply ContinuousMap.ext
  intro w
  exact congrArg cube.toFun (cubeSimplex_firstFace_factorization σ w)

/-- The last face of a triangulated smooth cube is precisely a simplex of its lower cube face. -/
theorem triangulatedCubeSimplex_lastFace
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (CubicalTriangulation.triangulatedCubeSimplex cube σ).comp (ContinuousFormulas.standardSimplexFace (Fin.last (n + 1))) =
      CubicalTriangulation.triangulatedCubeSimplex (DeRham.Comparison.StokesF.SingularCubeStokes.singularFace cube (σ (Fin.last n)) 0)
        (eraseCubePermutation σ (Fin.last n)) := by
  apply ContinuousMap.ext
  intro w
  exact congrArg cube.toFun (cubeSimplex_lastFace_factorization σ w)

/-- The first endpoint identity also holds as equality in the actual smooth
singular simplicial set, so it can be used directly in its chain complex. -/
theorem triangulatedCubeSmoothSimplex_firstFace
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.δ (0 : Fin (n + 2))
        (CubicalTriangulation.triangulatedCubeSmoothSimplex cube σ) =
      CubicalTriangulation.triangulatedCubeSmoothSimplex
        (DeRham.Comparison.StokesF.SingularCubeStokes.singularFace cube (σ 0) 1) (eraseCubePermutation σ 0) := by
  apply Subtype.ext
  apply ((TopCat.of (Fin m → ℝ)).toSSetObjEquiv (op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro w
  change cube.toFun
      (CubicalTriangulation.cubeSimplexLinearMap σ (Convexity.StdSimplex.map (0 : Fin (n + 2)).succAbove w)) =
    cube.toFun (DeRham.Comparison.StokesF.SingularCubeStokes.faceInclusion (σ 0) 1
      (CubicalTriangulation.cubeSimplexLinearMap (eraseCubePermutation σ 0) w))
  exact congrArg cube.toFun (cubeSimplex_firstFace_factorization σ w)

/-- The last endpoint identity holds in the actual smooth singular simplicial set. -/
theorem triangulatedCubeSmoothSimplex_lastFace
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.δ (Fin.last (n + 1))
        (CubicalTriangulation.triangulatedCubeSmoothSimplex cube σ) =
      CubicalTriangulation.triangulatedCubeSmoothSimplex
        (DeRham.Comparison.StokesF.SingularCubeStokes.singularFace cube (σ (Fin.last n)) 0)
        (eraseCubePermutation σ (Fin.last n)) := by
  apply Subtype.ext
  apply ((TopCat.of (Fin m → ℝ)).toSSetObjEquiv (op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro w
  change cube.toFun
      (CubicalTriangulation.cubeSimplexLinearMap σ (Convexity.StdSimplex.map (Fin.last (n + 1)).succAbove w)) =
    cube.toFun (DeRham.Comparison.StokesF.SingularCubeStokes.faceInclusion (σ (Fin.last n)) 0
      (CubicalTriangulation.cubeSimplexLinearMap (eraseCubePermutation σ (Fin.last n)) w))
  exact congrArg cube.toFun (cubeSimplex_lastFace_factorization σ w)

end

end OAI.AlgebraicTopology.Cohomology.Singular.CubicalEndpointFaces
