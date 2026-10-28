import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImmersionSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsoPrincipalDivisor

/-! # Principal Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.PrincipalCycle

noncomputable section

/-! A principal divisor on an integral closed subscheme gives the exact
native principal-cycle relation on its ambient reduced support. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {Z : Scheme} [IsIntegral Z]
  [AlgebraicGeometry.IsNoetherian Z] (i : Z ⟶ X.carrier) [IsClosedImmersion i]

theorem exists_native (p : ℕ) (g : Z.functionField) (hg : g ≠ 0) :
    ∃ h : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Geometric.StratumClosure.integralImageClosure i)).functionField, h ≠ 0 ∧
      CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward i (Affine.DivisorNorm.rationalPrincipalDivisor Z g)) =
        Principal.ClosedSectionCycle.principalCycle X p (CycleClass.Geometric.StratumClosure.integralImageClosure i) h := by
  let A := CycleClass.Geometric.StratumClosure.integralImageClosure i
  let e : Z ≅ CycleClass.Geometric.GenericPoint.reducedSupportScheme A := ImmersionSupport.supportIso i
  let h := (Divisor.DivisorRestriction.openFieldIso e.hom).inv g
  have hh : Divisor.DivisorRestriction.openFieldMap e.hom h = g :=
    ConcreteCategory.congr_hom (Divisor.DivisorRestriction.openFieldIso e.hom).inv_hom_id g
  have hη : e.hom (genericPoint Z) = genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme A) :=
    genericPoint_eq_of_isOpenImmersion e.hom
  have hpush := IsoPrincipalDivisor.pushforward e.hom hη h
  change CyclePushforward.pointPushforward e.hom (Affine.DivisorNorm.rationalPrincipalDivisor Z
    (Divisor.DivisorRestriction.openFieldMap e.hom h)) = _ at hpush
  rw [hh] at hpush
  refine ⟨h, ?_, ?_⟩
  · intro hz
    apply hg
    rw [← hh, hz, map_zero]
  · rw [Principal.ClosedSectionCycle.principalCycle_eq_pushforward]
    have he : CyclePushforward.pointPushforward i (Affine.DivisorNorm.rationalPrincipalDivisor Z g) =
        CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι A) (Affine.DivisorNorm.rationalPrincipalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme A) h) := by
      rw [← ImmersionSupport.supportIso_fac i, CyclePushforward.pointPushforward_comp]
      change CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι A)
        (CyclePushforward.pointPushforward e.hom (Affine.DivisorNorm.rationalPrincipalDivisor Z g)) = _
      rw [hpush]
    exact congrArg (CyclePushforward.degreeComponent X p) he

theorem isPrincipal (p : ℕ) (hp : X.supportCodimension (CycleClass.Geometric.StratumClosure.integralImageClosure i) + 1 = p)
    (g : Z.functionField) (hg : g ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.IsPrincipalDivisor X p (CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward i (Affine.DivisorNorm.rationalPrincipalDivisor Z g))) := by
  obtain ⟨h, hh, he⟩ := exists_native X i p g hg
  rw [he]
  exact Principal.ClosedSectionCycle.principalCycle_isPrincipalDivisor X p (CycleClass.Geometric.StratumClosure.integralImageClosure i) hp h hh

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.PrincipalCycle
