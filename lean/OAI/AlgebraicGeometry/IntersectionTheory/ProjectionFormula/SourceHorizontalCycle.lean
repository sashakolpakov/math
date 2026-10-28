import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFamilyGrading
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalHorizontalCycle

/-! # Source Horizontal Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceHorizontalCycle

noncomputable section

/-! Intrinsic source-family cycles have their exact native parameter
weights at every good endpoint and rationally equivalent endpoints. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyOnSource.Family

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)

theorem supported (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A))
    (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ CompactHorizontalFamilyFiber.Family.parameter X A) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme D)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0) :
    ((HorizontalFamilyFiber.Family.cycle (Projective.FamilyOnSource.Family.space X A) D (CompactHorizontalFamilyFiber.Family.parameter X A) hη a).support :
      Set (Projective.FamilyOnSource.Family.space X A)) ⊆ Set.range (Projective.FamilyOnSource.Family.specialization X A a ha) := by
  intro y hy
  rw [SourceEndpointFiber.range]
  change CompactHorizontalFamilyFiber.Family.parameter X A y = Affine.ParameterFiber.point ℂ a
  exact HorizontalFiberDimension.parameter (Projective.FamilyOnSource.Family.space X A) D
    (CompactHorizontalFamilyFiber.Family.parameter X A) hη a y (Finsupp.mem_support_iff.mp hy)

def cycle (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A))
    (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ CompactHorizontalFamilyFiber.Family.parameter X A) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme D)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)) (p : ℕ) (a : ℂ) :
    X.RationalDimensionCycle p :=
  CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A)
    (HorizontalFamilyFiber.Family.cycle (Projective.FamilyOnSource.Family.space X A) D (CompactHorizontalFamilyFiber.Family.parameter X A) hη a))

theorem coefficient (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A))
    (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ CompactHorizontalFamilyFiber.Family.parameter X A) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme D)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (p : ℕ) (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (B : X.DimensionCycleSupport p) :
    cycle X A D hη p a B =
      GlobalParameterSum.Weights.weight (Projective.FamilyOnSource.Family.space X A) (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint B.val))
        (Affine.ParameterFiber.germ ℂ (CompactHorizontalFamilyFiber.Family.parameter X A)
          (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint B.val)) a) D := by
  let := Projective.FamilySections.Family.source_closed X A a ha
  rw [cycle, Principal.ClosedSectionCycle.degreeComponent_apply,
    Principal.ClosedSectionCycle.apply (Projective.FamilyOnSource.Family.specialization X A a ha) (Projective.FamilyOnSource.Family.toSource X A)
      (Projective.FamilyOnSource.Family.specialization_source X A a ha) _ (supported X A D hη a ha), HorizontalFamilyFiber.Family.apply]

theorem rationallyEquivalent (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A))
    (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ CompactHorizontalFamilyFiber.Family.parameter X A) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme D)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (a b : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (hb : (Polynomial.MatrixPath.determinant A).eval b ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p (cycle X A D hη p a) (cycle X A D hη p b) :=
  HorizontalFamilyGrading.Family.rationallyEquivalent X A D hη m p a b ha hb

def weighted (c : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A) → ℚ) (F : Finset (IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A)))
    (p : ℕ) (a : ℂ) : X.RationalDimensionCycle p :=
  ∑ D ∈ F, if hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ CompactHorizontalFamilyFiber.Family.parameter X A) ≫
      Projective.FamilyIs.MatrixParameterOpen.affine) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme D)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) then
    c D • cycle X A D hη p a else 0

theorem weighted_coefficient (c : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A) → ℚ)
    (F : Finset (IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A))) (p : ℕ) (a : ℂ)
    (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0) (B : X.DimensionCycleSupport p) :
    weighted X A c F p a B =
      ∑ D ∈ F, c D * GlobalParameterSum.Weights.weight (Projective.FamilyOnSource.Family.space X A)
        (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint B.val))
        (Affine.ParameterFiber.germ ℂ (CompactHorizontalFamilyFiber.Family.parameter X A)
          (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint B.val)) a) D := by
  rw [weighted, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro D _
  split_ifs with hη
  · rw [Finsupp.smul_apply, coefficient X A D hη p a ha, smul_eq_mul]
  · rw [Finsupp.zero_apply, GlobalWeightSupport.nonhorizontal _ _ D hη, mul_zero]

theorem weighted_equivalent (c : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A) → ℚ)
    (F : Finset (IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A))) (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (a b : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (hb : (Polynomial.MatrixPath.determinant A).eval b ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p (weighted X A c F p a) (weighted X A c F p b) := by
  change (∑ D ∈ F, _) - (∑ D ∈ F, _) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p
  rw [← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro D _
  split_ifs with hη
  · rw [← smul_sub]
    exact (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p).smul_mem (c D)
      (rationallyEquivalent X A D hη m p a b ha hb)
  · rw [sub_self]
    exact (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p).zero_mem

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceHorizontalCycle
