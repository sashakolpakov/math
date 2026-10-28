import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CompactFamilyComponent
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFamilyFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Polynomial
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.CycleTransport

/-! # Compact Horizontal Family Fiber -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CompactHorizontalFamilyFiber

noncomputable section

/-! The open fibers of the proper component pencil are exactly the
native horizontal family cycles pushed to X, with their divisor weights. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Polynomial

namespace Family

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)

def parameter : Projective.FamilyOnSource.Family.space X A ⟶ Spec (.of ℂ[X]) :=
  Projective.FamilySections.Family.parameter X A ≫ Parameter.Polynomial.IntegralProduct.toLine A

variable (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A))

theorem parameter_comp :
    CompactFamilyComponent.Family.map X A D ≫
      CompactSupportPencil.parameter X (CompactFamilyComponent.Family.support X A D) =
    (CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ parameter X A) ≫ Projective.FamilyIs.MatrixParameterOpen.affine := by
  rw [CompactFamilyComponent.Family.map_parameter]
  simp only [parameter, Projective.FamilyIs.MatrixParameterOpen.inclusion, Parameter.Polynomial.IntegralProduct.toLine,
    Category.assoc]

variable (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ parameter X A) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
  (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme D)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))

include hη in
theorem horizontal : CompactSupportPencil.parameter X (CompactFamilyComponent.Family.support X A D)
    (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme (CompactFamilyComponent.Family.support X A D))) =
      genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) := by
  apply CompactFamilyComponent.Family.horizontal X A D
  simpa only [parameter, Projective.FamilyIs.MatrixParameterOpen.inclusion, Parameter.Polynomial.IntegralProduct.toLine,
    Category.assoc] using hη

theorem fiber (p : ℕ) (a : ℂ) :
    CompactFamilyComponent.Family.fiber X A D (horizontal X A D hη) p a =
    CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A)
      (HorizontalFamilyFiber.Family.cycle (Projective.FamilyOnSource.Family.space X A) D
        (parameter X A) hη a)) := by
  rw [Parameter.CycleTransport.family_formula]
  exact Parameter.CycleTransport.proper_formula X
    (CompactSupportPencil.source X (CompactFamilyComponent.Family.support X A D))
    (CompactFamilyComponent.Family.map X A D)
    (CompactSupportPencil.parameter X (CompactFamilyComponent.Family.support X A D))
    (horizontal X A D hη) (CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ Projective.FamilyOnSource.Family.toSource X A)
    ((CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ parameter X A) ≫ Projective.FamilyIs.MatrixParameterOpen.affine) hη
    (CompactFamilyComponent.Family.map_source X A D) (parameter_comp X A D) p a

theorem rationallyEquivalent (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension D
      (Projective.FamilyOnSource.Family.toSource X A ≫ X.structureMap) + p = m + 1)
    (a b : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (hb : (Polynomial.MatrixPath.determinant A).eval b ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p
      (CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A)
        (HorizontalFamilyFiber.Family.cycle (Projective.FamilyOnSource.Family.space X A) D (parameter X A) hη a)))
      (CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A)
        (HorizontalFamilyFiber.Family.cycle (Projective.FamilyOnSource.Family.space X A) D (parameter X A) hη b))) := by
  rw [← fiber X A D hη p a, ← fiber X A D hη p b]
  exact CompactFamilyComponent.Family.rationallyEquivalent X A D (horizontal X A D hη) m p hd a b ha hb

end Family

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CompactHorizontalFamilyFiber
