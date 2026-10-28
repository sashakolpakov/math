import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace
import Mathlib.RingTheory.FiniteType

/-! # Projective Space Finite Type -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpaceFiniteType

noncomputable section

/-! Finite generation of the homogeneous coordinate ring over its degree-zero ring. -/

/-- The polynomial coordinate ring is finitely generated as an algebra over
its actual degree-zero coefficient ring. -/
instance homogeneousCoordinateRing_finiteType_over_zero (n : ℕ) :
    Algebra.FiniteType (ProjectiveSpace.projectiveGrading n 0) (ProjectiveSpace.homogeneousCoordinateRing n) := by
  let : IsScalarTower ℂ (ProjectiveSpace.projectiveGrading n 0) (ProjectiveSpace.homogeneousCoordinateRing n) :=
    IsScalarTower.of_algebraMap_eq
      (R := ℂ) (S := ProjectiveSpace.projectiveGrading n 0) (A := ProjectiveSpace.homogeneousCoordinateRing n)
      (fun _ => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    ℂ (ProjectiveSpace.projectiveGrading n 0) (ProjectiveSpace.homogeneousCoordinateRing n)

end

end OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpaceFiniteType
