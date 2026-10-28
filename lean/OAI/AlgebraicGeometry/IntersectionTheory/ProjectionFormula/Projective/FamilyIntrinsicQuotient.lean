import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.FamilyQuotient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyStalkQuotient

/-! # Family Intrinsic Quotient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyIntrinsicQuotient

noncomputable section

/-! Native family-support modules specialize to native endpoint
support modules for the actual projective matrix-family embeddings. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace FamilyIntrinsic

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Polynomial.ProjectiveSubschemeFamily OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImmersionSupport

variable {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)
  {Z : Scheme} [IsIntegral Z] [IsLocallyNoetherian Z] (i : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
  (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
  (j : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) [IsClosedImmersion j]
  (J : Parameter.Polynomial.ProjectiveSubschemeFamily.space A i ⟶ MatrixFamily.Family.space A) [IsClosedImmersion J]
  (h : j ≫ MatrixFamily.Family.specialization A a ha = Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i a ha ≫ J)
  (ht : J ≫ FamilyRegularity.IntegralFamilySupport.parameterLine A =
    Parameter.Polynomial.ProjectiveSubschemeFamily.parameter A i ≫ Parameter.Polynomial.IntegralProduct.toLine A)

def equiv (z : Z)
    (hy : MatrixFamily.Family.specialization A a ha (j z) ∈
      (Closed.ImmersionSupport.support J : Set (MatrixFamily.Family.space A))) :
    QuotSMulTop
      (Affine.ParameterFiber.germ ℂ (FamilyRegularity.IntegralFamilySupport.parameterLine A)
        (MatrixFamily.Family.specialization A a ha (j z)) a)
      (CycleClass.Thom.IntersectionGeometry.localSupportModule (MatrixFamily.Family.space A) (Closed.ImmersionSupport.support J)
        (MatrixFamily.Family.specialization A a ha (j z)) hy) ≃ₗ[
          (MatrixFamily.Family.space A).presheaf.stalk
            (MatrixFamily.Family.specialization A a ha (j z))]
      ((ModuleCat.restrictScalars ((MatrixFamily.Family.specialization A a ha).stalkMap (j z)).hom).obj
        (CycleClass.Thom.IntersectionGeometry.localSupportModule (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (Closed.ImmersionSupport.support j) (j z) (Closed.ImageStalkModule.mem j z))) := by
  let : IsClosedImmersion (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i a ha) :=
    Parameter.FamilyKernel.Family.closed A (i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (Parameter.Polynomial.ProjectiveSubschemeFamily.parameter A i) (Parameter.Polynomial.ProjectiveSubschemeFamily.toSource A i)
      (Parameter.Polynomial.ProjectiveSubschemeFamily.base_change A i) a ha (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i a ha)
      (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization_source A i a ha) (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization_parameter A i a ha)
  apply Closed.FamilyQuotient.Family.equiv J j (MatrixFamily.Family.specialization A a ha)
    (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i a ha) h (FamilyRegularity.IntegralFamilySupport.parameterLine A) a z hy
  exact (FamilyStalkQuotient.Family.source_kernel A a ha i z).trans
    (congrArg (fun q => Ideal.span {Affine.ParameterFiber.germ ℂ q (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i a ha z) a}) ht.symm)

def equiv_at (z : Z) (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (hx : j z = x)
    (hxj : x ∈ (Closed.ImmersionSupport.support j : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)))
    (hy : MatrixFamily.Family.specialization A a ha x ∈
      (Closed.ImmersionSupport.support J : Set (MatrixFamily.Family.space A))) :
    QuotSMulTop
      (Affine.ParameterFiber.germ ℂ (FamilyRegularity.IntegralFamilySupport.parameterLine A)
        (MatrixFamily.Family.specialization A a ha x) a)
      (CycleClass.Thom.IntersectionGeometry.localSupportModule (MatrixFamily.Family.space A) (Closed.ImmersionSupport.support J)
        (MatrixFamily.Family.specialization A a ha x) hy) ≃ₗ[
          (MatrixFamily.Family.space A).presheaf.stalk
            (MatrixFamily.Family.specialization A a ha x)]
      ((ModuleCat.restrictScalars ((MatrixFamily.Family.specialization A a ha).stalkMap x).hom).obj
        (CycleClass.Thom.IntersectionGeometry.localSupportModule (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (Closed.ImmersionSupport.support j) x hxj)) := by
  subst x
  exact equiv A i a ha j J h ht z hy

end FamilyIntrinsic

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyIntrinsicQuotient
