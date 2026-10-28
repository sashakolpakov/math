import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFamilyGrading
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFiberClosedRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFamilyFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyRegularity

/-! # Contained Horizontal Family Fiber -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ContainedHorizontalFamilyFiber

noncomputable section

/-! An ambient horizontal component contained in the actual source
family gives a native source fiber cycle with the same embedded
multiplicities and equivalent good endpoint classes. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Family

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)

theorem parameter : Projective.FamilyOnSource.Family.toAmbient X A ≫
    Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A = CompactHorizontalFamilyFiber.Family.parameter X A := by
  change Projective.FamilyOnSource.Family.toAmbient X A ≫
    (Relative.ProjectiveI.Base.base (Polynomial.MatrixPath.Ring A) X.ambientDimension ≫
      Parameter.Polynomial.IntegralProduct.toLine A) =
    (Projective.FamilyOnSource.Family.toAmbient X A ≫
      Relative.ProjectiveI.Base.base (Polynomial.MatrixPath.Ring A) X.ambientDimension) ≫
        Parameter.Polynomial.IntegralProduct.toLine A
  exact (Category.assoc _ _ _).symm

variable (C : IrreducibleCloseds (Projective.MatrixFamily.Family.space A))
  (hC : (C : Set (Projective.MatrixFamily.Family.space A)) ⊆ Set.range (Projective.FamilyOnSource.Family.toAmbient X A))

abbrev support : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A) :=
  Closed.SupportRestriction.support (Projective.FamilyOnSource.Family.toAmbient X A) C hC

variable (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A) ≫
  Projective.FamilyIs.MatrixParameterOpen.affine) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))

include hη in
theorem horizontal : ((CycleClass.Geometric.GenericPoint.reducedSupportι (support X A C hC) ≫ CompactHorizontalFamilyFiber.Family.parameter X A) ≫
    Projective.FamilyIs.MatrixParameterOpen.affine) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme (support X A C hC))) =
      genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) := by
  have h := HorizontalFiberClosedRestriction.horizontal (Projective.FamilyOnSource.Family.toAmbient X A) C hC
    (Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A) hη
  rw [parameter] at h
  exact h

def cycle (a : ℂ) : Projective.FamilyOnSource.Family.space X A →₀ ℚ :=
  HorizontalFamilyFiber.Family.cycle (Projective.FamilyOnSource.Family.space X A) (support X A C hC)
    (CompactHorizontalFamilyFiber.Family.parameter X A) (horizontal X A C hC hη) a

theorem pushforward (a : ℂ) : CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toAmbient X A)
    (cycle X A C hC hη a) = HorizontalFamilyFiber.Family.cycle (Projective.MatrixFamily.Family.space A) C
      (Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A) hη a := by
  have he := HorizontalFamilyFiber.ParameterChange.cycle (support X A C hC) (parameter X A)
    (HorizontalFiberClosedRestriction.horizontal (Projective.FamilyOnSource.Family.toAmbient X A) C hC
      (Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A) hη) (horizontal X A C hC hη) a
  exact (congrArg (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toAmbient X A)) he.symm).trans
    (HorizontalFiberClosedRestriction.cycle (Projective.FamilyOnSource.Family.toAmbient X A) C hC
      (Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A) hη a)

theorem rationallyEquivalent (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (a b : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (hb : (Polynomial.MatrixPath.determinant A).eval b ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p
      (CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A) (cycle X A C hC hη a)))
      (CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A) (cycle X A C hC hη b))) :=
  HorizontalFamilyGrading.Family.rationallyEquivalent X A (support X A C hC) (horizontal X A C hC hη)
    m p a b ha hb

end Family

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ContainedHorizontalFamilyFiber
