import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceConstantFamily
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.FamilyQuotient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyStalkQuotient

/-! # Source Constant Quotient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceConstantQuotient

noncomputable section

/-! The actual scalar fiber of a constant source support has the
native support module on X. Both the ambient and support stalk
quotients use the same intrinsic parameter germ. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceConstantFamily.Family

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)
  (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)

theorem ambient_kernel (x : X.carrier) :
    RingHom.ker ((Projective.FamilyOnSource.Family.specialization X A a ha).stalkMap x).hom =
      Ideal.span {Affine.ParameterFiber.germ ℂ (CompactHorizontalFamilyFiber.Family.parameter X A)
        (Projective.FamilyOnSource.Family.specialization X A a ha x) a} :=
  Projective.FamilyStalkQuotient.Family.source_kernel A a ha X.embedding x

theorem reduced_support (B : IrreducibleCloseds X.carrier) :
    Closed.ImmersionSupport.support (CycleClass.Geometric.GenericPoint.reducedSupportι B) = B := by
  apply IrreducibleCloseds.ext
  rw [Flat.ClosedSupport.support_range, CycleClass.Geometric.GenericPoint.range_reducedSupportι]

def supportEquiv (Z : Scheme) (C D : IrreducibleCloseds Z) (h : C = D)
    (z : Z) (hzC : z ∈ (C : Set Z)) (hzD : z ∈ (D : Set Z)) :
    CycleClass.Thom.IntersectionGeometry.localSupportModule Z C z hzC ≃ₗ[Z.presheaf.stalk z] CycleClass.Thom.IntersectionGeometry.localSupportModule Z D z hzD := by
  subst D
  exact LinearEquiv.refl _ _

def equiv (B : IrreducibleCloseds X.carrier) (z : CycleClass.Geometric.GenericPoint.reducedSupportScheme B)
    (hy : Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Geometric.GenericPoint.reducedSupportι B z) ∈
      (SourceConstantFamily.Family.support X A B : Set (Projective.FamilyOnSource.Family.space X A))) :
    QuotSMulTop (Affine.ParameterFiber.germ ℂ (CompactHorizontalFamilyFiber.Family.parameter X A)
      (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Geometric.GenericPoint.reducedSupportι B z)) a)
      (CycleClass.Thom.IntersectionGeometry.localSupportModule (Projective.FamilyOnSource.Family.space X A) (SourceConstantFamily.Family.support X A B)
        (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Geometric.GenericPoint.reducedSupportι B z)) hy) ≃ₗ[
          (Projective.FamilyOnSource.Family.space X A).presheaf.stalk
            (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Geometric.GenericPoint.reducedSupportι B z))]
      (ModuleCat.restrictScalars ((Projective.FamilyOnSource.Family.specialization X A a ha).stalkMap
        (CycleClass.Geometric.GenericPoint.reducedSupportι B z)).hom).obj
        (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B (CycleClass.Geometric.GenericPoint.reducedSupportι B z) (by
          rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι B]
          exact Set.mem_range_self z)) := by
  let i := SourceConstantFamily.Family.embedding X B
  let s := Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i a ha
  let : IsClosedImmersion s :=
    Parameter.FamilyKernel.Family.closed A (i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension)
      (Parameter.Polynomial.ProjectiveSubschemeFamily.parameter A i) (Parameter.Polynomial.ProjectiveSubschemeFamily.toSource A i)
      (Parameter.Polynomial.ProjectiveSubschemeFamily.base_change A i) a ha s
      (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization_source A i a ha)
      (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization_parameter A i a ha)
  have hk : RingHom.ker (s.stalkMap z).hom =
      Ideal.span {Affine.ParameterFiber.germ ℂ
        (SourceConstantFamily.Family.map X A B ≫ CompactHorizontalFamilyFiber.Family.parameter X A) (s z) a} :=
    (Projective.FamilyStalkQuotient.Family.source_kernel A a ha i z).trans
      (congrArg (fun t => Ideal.span {Affine.ParameterFiber.germ ℂ t (s z) a})
        (SourceConstantFamily.Family.parameterLine X A B).symm)
  have e := Closed.FamilyQuotient.Family.equiv (SourceConstantFamily.Family.map X A B) (CycleClass.Geometric.GenericPoint.reducedSupportι B)
    (Projective.FamilyOnSource.Family.specialization X A a ha) s (SourceConstantFamily.Family.section_square X A B a ha).symm
    (CompactHorizontalFamilyFiber.Family.parameter X A) a z hy hk
  let eB := supportEquiv X.carrier (Closed.ImmersionSupport.support (CycleClass.Geometric.GenericPoint.reducedSupportι B)) B
    (reduced_support X B) (CycleClass.Geometric.GenericPoint.reducedSupportι B z) (Closed.ImageStalkModule.mem (CycleClass.Geometric.GenericPoint.reducedSupportι B) z)
    (by rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι B]; exact Set.mem_range_self z)
  exact e.trans ((ModuleCat.restrictScalars
    ((Projective.FamilyOnSource.Family.specialization X A a ha).stalkMap (CycleClass.Geometric.GenericPoint.reducedSupportι B z)).hom).mapIso
      eB.toModuleIso).toLinearEquiv

def equiv_at (B : IrreducibleCloseds X.carrier) (z : CycleClass.Geometric.GenericPoint.reducedSupportScheme B)
    (x : X.carrier) (hz : CycleClass.Geometric.GenericPoint.reducedSupportι B z = x) (hx : x ∈ (B : Set X.carrier))
    (hy : Projective.FamilyOnSource.Family.specialization X A a ha x ∈
      (SourceConstantFamily.Family.support X A B : Set (Projective.FamilyOnSource.Family.space X A))) :
    QuotSMulTop (Affine.ParameterFiber.germ ℂ (CompactHorizontalFamilyFiber.Family.parameter X A)
      (Projective.FamilyOnSource.Family.specialization X A a ha x) a)
      (CycleClass.Thom.IntersectionGeometry.localSupportModule (Projective.FamilyOnSource.Family.space X A) (SourceConstantFamily.Family.support X A B)
        (Projective.FamilyOnSource.Family.specialization X A a ha x) hy) ≃ₗ[
          (Projective.FamilyOnSource.Family.space X A).presheaf.stalk
            (Projective.FamilyOnSource.Family.specialization X A a ha x)]
      (ModuleCat.restrictScalars ((Projective.FamilyOnSource.Family.specialization X A a ha).stalkMap x).hom).obj
        (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B x hx) := by
  subst x
  exact equiv X A a ha B z hy

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceConstantQuotient
