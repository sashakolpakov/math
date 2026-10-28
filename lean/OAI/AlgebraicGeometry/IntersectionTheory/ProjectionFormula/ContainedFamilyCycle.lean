import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ContainedHorizontalFamilyFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalHorizontalCycle

/-! # Contained Family Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ContainedFamilyCycle

noncomputable section

/-! Fixed ambient global components contained in the source family
give a finite source cycle with the exact ambient weighted cycle
and rationally equivalent good endpoints in all degrees. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Family

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)
  (c : IrreducibleCloseds (Projective.MatrixFamily.Family.space A) → ℚ)
  (F : Finset (IrreducibleCloseds (Projective.MatrixFamily.Family.space A)))

def cycle (a : ℂ) : Projective.FamilyOnSource.Family.space X A →₀ ℚ :=
  ∑ C ∈ F, if hC : (C : Set (Projective.MatrixFamily.Family.space A)) ⊆
      Set.range (Projective.FamilyOnSource.Family.toAmbient X A) then
    if hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A) ≫
      Projective.FamilyIs.MatrixParameterOpen.affine) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) then
      c C • ContainedHorizontalFamilyFiber.Family.cycle X A C hC hη a
    else 0
  else 0

theorem pushforward (hF : ∀ C ∈ F, (C : Set (Projective.MatrixFamily.Family.space A)) ⊆
    Set.range (Projective.FamilyOnSource.Family.toAmbient X A)) (a : ℂ) :
    CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toAmbient X A) (cycle X A c F a) =
    GlobalHorizontalCycle.cycle (Projective.MatrixFamily.Family.space A)
      (Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A) c F a := by
  rw [cycle, map_sum, GlobalHorizontalCycle.cycle]
  apply Finset.sum_congr rfl
  intro C hC
  rw [dite_eq_left (hF C hC)]
  split_ifs with hη
  · rw [map_smul, ContainedHorizontalFamilyFiber.Family.pushforward]
  · exact map_zero _

theorem projection (hF : ∀ C ∈ F, (C : Set (Projective.MatrixFamily.Family.space A)) ⊆
    Set.range (Projective.FamilyOnSource.Family.toAmbient X A)) (a : ℂ) :
    CyclePushforward.pointPushforward X.embedding
      (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A) (cycle X A c F a)) =
    CyclePushforward.pointPushforward (Projective.FamilySupport.Family.projection A)
      (GlobalHorizontalCycle.cycle (Projective.MatrixFamily.Family.space A)
        (Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A) c F a) := by
  have he : Projective.FamilyOnSource.Family.toSource X A ≫ X.embedding =
      Projective.FamilyOnSource.Family.toAmbient X A ≫ Projective.FamilySupport.Family.projection A :=
    (pullback.condition (f := Projective.FamilySupport.Family.projection A) (g := X.embedding)).symm
  rw [← LinearMap.comp_apply, ← CyclePushforward.pointPushforward_comp, he, CyclePushforward.pointPushforward_comp, LinearMap.comp_apply,
    pushforward X A c F hF a]

theorem rationallyEquivalent (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (a b : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (hb : (Polynomial.MatrixPath.determinant A).eval b ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p
      (CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A) (cycle X A c F a)))
      (CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A) (cycle X A c F b))) := by
  simp only [cycle, map_sum]
  change (∑ C ∈ F, _) - (∑ C ∈ F, _) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p
  rw [← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro C _
  by_cases hC : (C : Set (Projective.MatrixFamily.Family.space A)) ⊆
      Set.range (Projective.FamilyOnSource.Family.toAmbient X A)
  · rw [dite_eq_left hC, dite_eq_left hC]
    by_cases hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A) ≫
        Projective.FamilyIs.MatrixParameterOpen.affine) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)
    · rw [dite_eq_left hη, dite_eq_left hη, map_smul, map_smul, map_smul, map_smul, ← smul_sub]
      exact (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p).smul_mem (c C)
        (ContainedHorizontalFamilyFiber.Family.rationallyEquivalent X A C hC hη m p a b ha hb)
    · simp only [dite_eq_right hη, map_zero, sub_self]
      exact (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p).zero_mem
  · simp only [dite_eq_right hC, map_zero, sub_self]
    exact (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p).zero_mem

end Family

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ContainedFamilyCycle
