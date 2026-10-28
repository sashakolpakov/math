import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveI
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormMatrix

/-! # Matrix Family -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.MatrixFamily

noncomputable section

/-! The polynomial matrix path yields a projective automorphism over
its parameter ring. The marked endpoint specializations are exactly
the identity and the prescribed projective linear automorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Family

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath

variable {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)

abbrev space : Scheme := Relative.ProjectiveLinear.space (Polynomial.MatrixPath.Ring A) n

def automorphism : space A ≅ space A := Relative.ProjectiveLinear.iso (Polynomial.MatrixPath.unit A)

def specialization (t : ℂ) (ht : (Polynomial.MatrixPath.determinant A).eval t ≠ 0) : Foundations.Scheme.ProjectiveSpace.projectiveSpace n ⟶ space A :=
  Relative.ProjectiveI.Scalars.map (Polynomial.MatrixPath.evaluation A t ht) n

theorem over_base : (automorphism A).hom ≫ Relative.ProjectiveI.Base.base (Polynomial.MatrixPath.Ring A) n =
    Relative.ProjectiveI.Base.base (Polynomial.MatrixPath.Ring A) n := Relative.ProjectiveI.Base.matrix_over (Polynomial.MatrixPath.unit A)

theorem specialization_base (t : ℂ) (ht : (Polynomial.MatrixPath.determinant A).eval t ≠ 0) :
    specialization A t ht ≫ Relative.ProjectiveI.Base.base (Polynomial.MatrixPath.Ring A) n =
      Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n ≫ Spec.map (CommRingCat.ofHom (Polynomial.MatrixPath.evaluation A t ht)) :=
  Relative.ProjectiveI.Base.scalar_over (Polynomial.MatrixPath.evaluation A t ht) n

theorem at_zero : specialization A 0 (Polynomial.MatrixPath.zero_good A) ≫ (automorphism A).hom =
    specialization A 0 (Polynomial.MatrixPath.zero_good A) := by
  have h := Relative.ProjectiveI.Scalars.naturality (Polynomial.MatrixPath.evaluation A 0 (Polynomial.MatrixPath.zero_good A)) n (Polynomial.MatrixPath.unit A)
  have hu : Relative.ProjectiveI.Scalars.unit (Polynomial.MatrixPath.evaluation A 0 (Polynomial.MatrixPath.zero_good A)) n (Polynomial.MatrixPath.unit A) = 1 :=
    Units.ext (Polynomial.MatrixPath.evaluate_zero A (Polynomial.MatrixPath.zero_good A))
  rw [hu, Relative.ProjectiveLinear.map_one, Category.id_comp] at h
  exact h.symm

theorem at_one : specialization A 1 (Polynomial.MatrixPath.one_good A) ≫ (automorphism A).hom =
    LinearChart.Automorphism.map A ≫ specialization A 1 (Polynomial.MatrixPath.one_good A) := by
  have h := Relative.ProjectiveI.Scalars.naturality (Polynomial.MatrixPath.evaluation A 1 (Polynomial.MatrixPath.one_good A)) n (Polynomial.MatrixPath.unit A)
  have hu : Relative.ProjectiveI.Scalars.unit (Polynomial.MatrixPath.evaluation A 1 (Polynomial.MatrixPath.one_good A)) n (Polynomial.MatrixPath.unit A) = A :=
    Units.ext (Polynomial.MatrixPath.evaluate_one A (Polynomial.MatrixPath.one_good A))
  rw [hu] at h
  exact h.symm

theorem at_linear_form (e : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :
    specialization (LinearFormMatrix.unit e) 1 (Polynomial.MatrixPath.one_good (LinearFormMatrix.unit e)) ≫
        (automorphism (LinearFormMatrix.unit e)).hom =
      LinearFormAutomorphism.map e ≫
        specialization (LinearFormMatrix.unit e) 1 (Polynomial.MatrixPath.one_good (LinearFormMatrix.unit e)) := by
  rw [at_one, LinearFormMatrix.map]

end Family

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.MatrixFamily
