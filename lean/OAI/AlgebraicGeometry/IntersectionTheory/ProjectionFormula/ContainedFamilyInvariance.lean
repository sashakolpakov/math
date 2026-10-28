import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceFiberIntersection
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ContainedFamilyCycle

/-! # Contained Family Invariance -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ContainedFamilyInvariance

noncomputable section

/-! The native proper-intersection invariance applies component by
component to every finite weighted family contained in the source. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Family

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyOnSource.Family OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem equivalent (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)
    (m p q : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (c : IrreducibleCloseds (Projective.MatrixFamily.Family.space A) → ℚ)
    (F : Finset (IrreducibleCloseds (Projective.MatrixFamily.Family.space A)))
    (B : X.DimensionCycleSupport q)
    (a b : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (hb : (Polynomial.MatrixPath.determinant A).eval b ≠ 0)
    (hproper_a : ∀ C ∈ F, ∀ hC : (C : Set (Projective.MatrixFamily.Family.space A)) ⊆ Set.range (Projective.FamilyOnSource.Family.toAmbient X A),
      ∀ E : IrreducibleCloseds X.carrier,
        (E : Set X.carrier) ⊆ (Projective.FamilyOnSource.Family.specialization X A a ha ⁻¹'
          (ContainedHorizontalFamilyFiber.Family.support X A C hC : Set (Projective.FamilyOnSource.Family.space X A))) ∩ (B.val : Set X.carrier) →
            p + q ≤ X.supportCodimension E)
    (hproper_b : ∀ C ∈ F, ∀ hC : (C : Set (Projective.MatrixFamily.Family.space A)) ⊆ Set.range (Projective.FamilyOnSource.Family.toAmbient X A),
      ∀ E : IrreducibleCloseds X.carrier,
        (E : Set X.carrier) ⊆ (Projective.FamilyOnSource.Family.specialization X A b hb ⁻¹'
          (ContainedHorizontalFamilyFiber.Family.support X A C hC : Set (Projective.FamilyOnSource.Family.space X A))) ∩ (B.val : Set X.carrier) →
            p + q ≤ X.supportCodimension E) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (p + q)
      (Supports.ProperCycle.intersectionBilinear X m p q
        (CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A) (ContainedFamilyCycle.Family.cycle X A c F a))) (Finsupp.single B 1))
      (Supports.ProperCycle.intersectionBilinear X m p q
        (CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A) (ContainedFamilyCycle.Family.cycle X A c F b))) (Finsupp.single B 1)) := by
  let L : (Projective.FamilyOnSource.Family.space X A →₀ ℚ) →ₗ[ℚ] X.RationalDimensionCycle (p + q) :=
    ((Supports.ProperCycle.intersectionBilinear X m p q).flip (Finsupp.single B 1)).comp
      ((CyclePushforward.degreeComponent X p).comp (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A)))
  change L (ContainedFamilyCycle.Family.cycle X A c F a) - L (ContainedFamilyCycle.Family.cycle X A c F b) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (p + q)
  rw [ContainedFamilyCycle.Family.cycle, ContainedFamilyCycle.Family.cycle, map_sum, map_sum, ← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro C hCF
  by_cases hC : (C : Set (Projective.MatrixFamily.Family.space A)) ⊆ Set.range (Projective.FamilyOnSource.Family.toAmbient X A)
  · rw [dite_eq_left hC, dite_eq_left hC]
    by_cases hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A) ≫
        Projective.FamilyIs.MatrixParameterOpen.affine) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)
    · rw [dite_eq_left hη, dite_eq_left hη, map_smul, map_smul, ← smul_sub]
      apply (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (p + q)).smul_mem
      exact SourceFiberIntersection.FamilyInvariance.equivalent X A m p q
        (ContainedHorizontalFamilyFiber.Family.support X A C hC)
        (ContainedHorizontalFamilyFiber.Family.horizontal X A C hC hη) B a b ha hb
        (hproper_a C hCF hC) (hproper_b C hCF hC)
    · simp only [dite_eq_right hη, map_zero, sub_self]
      exact (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (p + q)).zero_mem
  · simp only [dite_eq_right hC, map_zero, sub_self]
    exact (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (p + q)).zero_mem

end Family

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ContainedFamilyInvariance
