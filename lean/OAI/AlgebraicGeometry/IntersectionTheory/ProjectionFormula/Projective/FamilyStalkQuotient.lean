import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.FamilyKernel
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyRegularity

/-! # Family Stalk Quotient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyStalkQuotient

noncomputable section

/-! The actual ambient and subscheme matrix-family endpoints have
the native stalk quotient by their intrinsic parameter germ. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace Family

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath

variable {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)
  (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)

theorem ambient_kernel (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :
    RingHom.ker ((MatrixFamily.Family.specialization A a ha).stalkMap x).hom =
      Ideal.span {Affine.ParameterFiber.germ ℂ (FamilyRegularity.IntegralFamilySupport.parameterLine A)
        (MatrixFamily.Family.specialization A a ha x) a} :=
  Parameter.FamilyKernel.Family.kernel A (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
    (Relative.ProjectiveI.Base.base (Polynomial.MatrixPath.Ring A) n) (FamilySupport.Family.projection A)
    (Relative.ProjectivePullback.isPullback (FamilySupport.Family.coefficients A) n).flip
    a ha (MatrixFamily.Family.specialization A a ha)
    (FamilySupport.Family.specialization_projection A a ha)
    (MatrixFamily.Family.specialization_base A a ha) x

def ambientEquiv (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :
    ((MatrixFamily.Family.space A).presheaf.stalk
        (MatrixFamily.Family.specialization A a ha x) ⧸
      Ideal.span {Affine.ParameterFiber.germ ℂ (FamilyRegularity.IntegralFamilySupport.parameterLine A)
        (MatrixFamily.Family.specialization A a ha x) a}) ≃+*
      (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.stalk x :=
  Parameter.FamilyKernel.Family.quotientEquiv A (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
    (Relative.ProjectiveI.Base.base (Polynomial.MatrixPath.Ring A) n) (FamilySupport.Family.projection A)
    (Relative.ProjectivePullback.isPullback (FamilySupport.Family.coefficients A) n).flip
    a ha (MatrixFamily.Family.specialization A a ha)
    (FamilySupport.Family.specialization_projection A a ha)
    (MatrixFamily.Family.specialization_base A a ha) x

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Polynomial.ProjectiveSubschemeFamily

variable {Z : Scheme} (i : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n)

theorem source_kernel (z : Z) : RingHom.ker ((Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i a ha).stalkMap z).hom =
    Ideal.span {Affine.ParameterFiber.germ ℂ
      (Parameter.Polynomial.ProjectiveSubschemeFamily.parameter A i ≫ Parameter.Polynomial.IntegralProduct.toLine A) (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i a ha z) a} :=
  Parameter.FamilyKernel.Family.kernel A (i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (Parameter.Polynomial.ProjectiveSubschemeFamily.parameter A i) (Parameter.Polynomial.ProjectiveSubschemeFamily.toSource A i)
    (Parameter.Polynomial.ProjectiveSubschemeFamily.base_change A i) a ha (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i a ha)
    (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization_source A i a ha) (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization_parameter A i a ha) z

def sourceEquiv (z : Z) :
    ((Parameter.Polynomial.ProjectiveSubschemeFamily.space A i).presheaf.stalk (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i a ha z) ⧸
      Ideal.span {Affine.ParameterFiber.germ ℂ
        (Parameter.Polynomial.ProjectiveSubschemeFamily.parameter A i ≫ Parameter.Polynomial.IntegralProduct.toLine A) (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i a ha z) a}) ≃+*
      Z.presheaf.stalk z :=
  Parameter.FamilyKernel.Family.quotientEquiv A (i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (Parameter.Polynomial.ProjectiveSubschemeFamily.parameter A i) (Parameter.Polynomial.ProjectiveSubschemeFamily.toSource A i)
    (Parameter.Polynomial.ProjectiveSubschemeFamily.base_change A i) a ha (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i a ha)
    (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization_source A i a ha) (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization_parameter A i a ha) z

end Family

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyStalkQuotient
