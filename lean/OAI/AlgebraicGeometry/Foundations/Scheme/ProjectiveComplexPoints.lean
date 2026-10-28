import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectivePointInjective
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectivePointSurjective

/-! # Projective Complex Points -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveComplexPoints

noncomputable section

/-!
# Homogeneous coordinates classify actual complex projective scheme points

This equivalence uses the proved map from ordinary projectivization to scheme
morphisms, its injectivity by homogeneous linear equations, and its surjectivity
through the actual affine open charts of `Proj`. The codomain consists of genuine
morphisms over `Spec ℂ`; no additional point structure is postulated.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- Ordinary complex projective space is exactly the set of actual complex
points of its standard projective scheme, over the specified complex base. -/
def projectiveComplexPointsEquiv (n : ℕ) :
    Projectivization ℂ (Fin (n + 1) → ℂ) ≃
      (Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ Over.mk (ProjectiveSpace.projectiveSpaceToBase n)) := by
  refine Equiv.ofBijective
    (fun p => Over.homMk (ProjectiveVectorScale.projectivizationPoint n p) (ProjectiveVectorScale.projectivizationPoint_over_base p))
    ⟨?_, ?_⟩
  · intro p q h
    apply ProjectivePointInjective.projectivizationPoint_injective n
    exact congrArg
      (fun r : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ Over.mk (ProjectiveSpace.projectiveSpaceToBase n) => r.left) h
  · intro q
    obtain ⟨p, hp⟩ := ProjectivePointSurjective.exists_projectivizationPoint q.left q.w
    exact ⟨p, Over.OverMorphism.ext hp⟩

/-- The equivalence uses the original homogeneous-coordinate scheme morphism. -/
@[simp]
theorem projectiveComplexPointsEquiv_apply (n : ℕ)
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) :
    projectiveComplexPointsEquiv n p =
      Over.homMk (ProjectiveVectorScale.projectivizationPoint n p) (ProjectiveVectorScale.projectivizationPoint_over_base p) := rfl

@[simp]
theorem projectiveComplexPointsEquiv_left (n : ℕ)
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) :
    (projectiveComplexPointsEquiv n p).left = ProjectiveVectorScale.projectivizationPoint n p := rfl

/-- Nonzero homogeneous vectors have their original, explicitly constructed
scheme points under the global equivalence. -/
@[simp]
theorem projectiveComplexPointsEquiv_mk_left {n : ℕ}
    (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    (projectiveComplexPointsEquiv n (Projectivization.mk ℂ v hv)).left =
      ProjectiveVectorPoint.projectiveVectorPoint v hv := rfl

/-- The inverse coordinate class recovers the given actual scheme morphism. -/
@[simp]
theorem projectiveComplexPointsEquiv_symm_left (n : ℕ)
    (q : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ Over.mk (ProjectiveSpace.projectiveSpaceToBase n)) :
    ProjectiveVectorScale.projectivizationPoint n ((projectiveComplexPointsEquiv n).symm q) = q.left :=
  congrArg
    (fun r : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ Over.mk (ProjectiveSpace.projectiveSpaceToBase n) => r.left)
    ((projectiveComplexPointsEquiv n).apply_symm_apply q)

/-- Actual coordinate open subschemes correspond to nonvanishing homogeneous
coordinate patches under the global equivalence. -/
theorem projectiveComplexPointsEquiv_mem_coordinateOpen (n : ℕ) (i : Fin (n + 1))
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) (x : ProjectiveSpace.complexBase) :
    (projectiveComplexPointsEquiv n p).left x ∈ ProjectiveCoordinateCover.projectiveCoordinateOpen n i ↔
      ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff]
    exact ProjectiveVectorPoint.projectiveVectorPoint_mem_coordinateOpen_iff v hv i x

/-- On each standard chart the equivalence is polynomial evaluation followed
by the genuine affine open immersion of the projective scheme. -/
theorem projectiveComplexPointsEquiv_affineChart_left (n : ℕ) (i : Fin (n + 1))
    (a : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    (projectiveComplexPointsEquiv n
      ((ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.affineChart i).symm a).val).left =
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval a)) ≫ ProjectiveChart.projectiveAffineChartMap n i := by
  change ProjectiveVectorPoint.projectiveVectorPoint (DehomogenizationC.Algebraic.Dehomogenization.insertOne i a)
    (ProjectiveChartPoint.insertOne_ne_zero n i a) = _
  exact (ProjectiveChartPoint.projectiveAffineChartMap_eval_eq_vectorPoint n i a (ProjectiveChartPoint.insertOne_ne_zero n i a)).symm

end

end OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveComplexPoints
