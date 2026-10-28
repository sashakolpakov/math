import OAI.AlgebraicTopology.Cohomology.Singular.CubicalTriangulation
import Mathlib.Data.Fin.Tuple.Basic

/-! # Cubical Faces -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.CubicalFaces

noncomputable section

/-!
# Faces of the permutation simplices in a cube

Internal faces agree for permutations differing by the adjacent swap of the
two directions bordering the omitted vertex. The first and last faces lie in
the corresponding upper and lower cube faces. The face maps below are
mathlib's actual standard-simplex maps, not abstract incidence assumptions.

These geometric identities are ingredients for a triangulation boundary
calculation. No chain-equivalence assertion is made here.
-/

open _root_.CategoryTheory Opposite
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex BigOperators Simplicial ContDiff

variable {n m : ℕ}

private def barycentricTailSum (w : Fin (n + 1) → ℝ) (p : Fin n) : ℝ :=
  ∑ j : Fin (n + 1), if p.val < j.val then w j else 0

/-- The omitted coordinate of a genuine standard-simplex face is zero. -/
theorem standardSimplexFace_omitted_coordinate (k : Fin (n + 1))
    (w : Convexity.StdSimplex ℝ (Fin n)) :
    Convexity.StdSimplex.map k.succAbove w k = 0 := by
  exact Finsupp.mapDomain_of_notMem_range w.weights k (by simp)

/-- Adjacent tail sums agree when the barycentric coordinate between them vanishes. -/
theorem adjacentTailSums_eq (p q : Fin n) (hq : q.val = p.val + 1)
    (w : Fin (n + 1) → ℝ) (hw : w q.castSucc = 0) :
    (∑ j : Fin (n + 1), if p.val < j.val then w j else 0) =
      ∑ j : Fin (n + 1), if q.val < j.val then w j else 0 := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hjq : q.val < j.val
  · have hjp : p.val < j.val := by omega
    simp [hjq, hjp]
  · by_cases hjp : p.val < j.val
    · have hj : j = q.castSucc := by
        apply Fin.ext
        change j.val = q.val
        omega
      subst j
      simp [hw]
    · simp [hjq, hjp]

/-- Swapping adjacent coordinate directions does not change the affine map on
the hyperplane where their intervening barycentric coordinate is zero. -/
theorem cubeSimplexLinearMap_adjacentSwap (σ : Equiv.Perm (Fin n))
    (p q : Fin n) (hq : q.val = p.val + 1)
    (w : Fin (n + 1) → ℝ) (hw : w q.castSucc = 0) :
    CubicalTriangulation.cubeSimplexLinearMap σ w =
      CubicalTriangulation.cubeSimplexLinearMap ((Equiv.swap p q).trans σ) w := by
  funext a
  rw [CubicalTriangulation.cubeSimplexLinearMap_apply, CubicalTriangulation.cubeSimplexLinearMap_apply]
  change barycentricTailSum w (σ.symm a) =
    barycentricTailSum w (((Equiv.swap p q).trans σ).symm a)
  simp only [Equiv.symm_trans_apply, Equiv.symm_swap]
  by_cases hp : σ.symm a = p
  · rw [hp, Equiv.swap_apply_left]
    exact adjacentTailSums_eq p q hq w hw
  · by_cases hq' : σ.symm a = q
    · rw [hq', Equiv.swap_apply_right]
      exact (adjacentTailSums_eq p q hq w hw).symm
    · rw [Equiv.swap_apply_of_ne_of_ne hp hq']

/-- The two permutation simplices have exactly the same internal face. -/
theorem cubeSimplex_internalFace (σ : Equiv.Perm (Fin (n + 2)))
    (i : Fin (n + 1)) (w : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    CubicalTriangulation.cubeSimplexLinearMap σ (Convexity.StdSimplex.map i.succ.castSucc.succAbove w) =
      CubicalTriangulation.cubeSimplexLinearMap ((Equiv.swap i.castSucc i.succ).trans σ)
        (Convexity.StdSimplex.map i.succ.castSucc.succAbove w) := by
  apply cubeSimplexLinearMap_adjacentSwap σ i.castSucc i.succ rfl
  exact standardSimplexFace_omitted_coordinate i.succ.castSucc w

/-- On the face omitting the first vertex, the first permuted cube coordinate is one. -/
theorem cubeSimplex_firstCoordinate_eq_one (σ : Equiv.Perm (Fin (n + 1)))
    (w : Convexity.StdSimplex ℝ (Fin (n + 2))) (hw : w 0 = 0) :
    CubicalTriangulation.cubeSimplexLinearMap σ w (σ 0) = 1 := by
  rw [CubicalTriangulation.cubeSimplexLinearMap_apply]
  simp only [Equiv.symm_apply_apply, Fin.val_zero]
  calc
    (∑ j : Fin (n + 2), if 0 < j.val then w j else 0) = ∑ j : Fin (n + 2), w j := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = 0
      · subst j
        simp [hw]
      · have hpos : 0 < j.val := by
          have hne : j.val ≠ 0 := by
            intro h
            apply hj
            exact Fin.ext h
          omega
        simp [hpos]
    _ = 1 := w.total_of_fintype

/-- The last permuted coordinate is the last barycentric weight. -/
theorem cubeSimplex_lastCoordinate (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 2) → ℝ) :
    CubicalTriangulation.cubeSimplexLinearMap σ w (σ (Fin.last n)) = w (Fin.last (n + 1)) := by
  rw [CubicalTriangulation.cubeSimplexLinearMap_apply]
  simp only [Equiv.symm_apply_apply, Fin.val_last]
  rw [Finset.sum_eq_single (Fin.last (n + 1))]
  · simp
  · intro j _ hne
    have hj : ¬ n < j.val := by
      intro h
      apply hne
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    simp [hj]
  · simp

/-- The first simplex face lies in the upper face of its first permuted cube direction. -/
theorem cubeSimplex_firstFace_mem (σ : Equiv.Perm (Fin (n + 1)))
    (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    CubicalTriangulation.cubeSimplexLinearMap σ (Convexity.StdSimplex.map (0 : Fin (n + 2)).succAbove w) ∈
      DeRham.Comparison.StokesF.SingularCubeStokes.unitCube (n + 1) ∩ {x | x (σ 0) = 1} := by
  constructor
  · exact CubicalTriangulation.cubeSimplexLinearMap_mem_unitCube σ ⟨Convexity.StdSimplex.map _ w, rfl⟩
  · apply cubeSimplex_firstCoordinate_eq_one
    exact standardSimplexFace_omitted_coordinate 0 w

/-- The last simplex face lies in the lower face of its last permuted cube direction. -/
theorem cubeSimplex_lastFace_mem (σ : Equiv.Perm (Fin (n + 1)))
    (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    CubicalTriangulation.cubeSimplexLinearMap σ (Convexity.StdSimplex.map (Fin.last (n + 1)).succAbove w) ∈
      DeRham.Comparison.StokesF.SingularCubeStokes.unitCube (n + 1) ∩ {x | x (σ (Fin.last n)) = 0} := by
  constructor
  · exact CubicalTriangulation.cubeSimplexLinearMap_mem_unitCube σ ⟨Convexity.StdSimplex.map _ w, rfl⟩
  · change CubicalTriangulation.cubeSimplexLinearMap σ
      (Convexity.StdSimplex.map (Fin.last (n + 1)).succAbove w) (σ (Fin.last n)) = 0
    rw [cubeSimplex_lastCoordinate]
    exact standardSimplexFace_omitted_coordinate (Fin.last (n + 1)) w

/-- The matching internal faces remain equal after composition with an actual smooth cube. -/
theorem triangulatedCubeSimplex_internalFace
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 2) m)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    (CubicalTriangulation.triangulatedCubeSimplex cube σ).comp
        ⟨Convexity.StdSimplex.map i.succ.castSucc.succAbove,
          Convexity.StdSimplex.continuous_map ℝ i.succ.castSucc.succAbove⟩ =
      (CubicalTriangulation.triangulatedCubeSimplex cube ((Equiv.swap i.castSucc i.succ).trans σ)).comp
        ⟨Convexity.StdSimplex.map i.succ.castSucc.succAbove,
          Convexity.StdSimplex.continuous_map ℝ i.succ.castSucc.succAbove⟩ := by
  apply ContinuousMap.ext
  intro w
  exact congrArg cube.toFun (cubeSimplex_internalFace σ i w)

end

end OAI.AlgebraicTopology.Cohomology.Singular.CubicalFaces
