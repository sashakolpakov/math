import OAI.AlgebraicGeometry.CycleClass.Thom.DivisorDescent
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalZero

/-! # Principal Descent -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalDescent

noncomputable section

/-! Every genuine principal-divisor relation has zero independently defined
geometric cycle class, in every codimension and on every presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.DivisorDescent.Constructions.PrincipalComponentRestriction OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport.Constructions
  Normalization.Principal.Constructions Normalization.PrincipalZero.Constructions.Class

theorem integralPrincipalDivisor_geometricClass_zero (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (W : IrreducibleCloseds V.carrier) (p : ℕ) (hp : Geometric.DimensionCycles.dimensionCodimension V W + 1 = p)
    (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)
    (d : Geometric.DimensionCycles.RationalDimensionCycle V p)
    (hd : ∀ C, d C = IntersectionGeometry.principalDivisorCoefficient V.presentation W g C.val) :
    V.geometricCycleClassMap p d = 0 := by
  subst p
  have he : d = Normalization.Principal.Constructions.normalizedPrincipalCycle V W g hg := by
    ext C
    exact (hd C).trans (Normalization.Principal.Constructions.normalizedPrincipalCycle_coefficient V W g hg C).symm
  rw [he]
  exact Normalization.PrincipalZero.Constructions.Class.normalizedPrincipalCycle_geometricClass_zero V W g hg

theorem principalDivisor_geometricClass_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (W : IrreducibleCloseds X.carrier) (hW : X.supportCodimension W + 1 = p)
    (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)
    (d : X.RationalDimensionCycle p)
    (hd : ∀ Z, d Z = IntersectionGeometry.principalDivisorCoefficient X W g Z.val) :
    X.geometricCycleClassMap p d = 0 := by
  obtain ⟨⟨C, B⟩, rfl⟩ := X.componentSupportEquiv.symm.surjective W
  change X.supportCodimension (X.componentSupportImage C B) + 1 = p at hW
  rw [X.supportCodimension_componentSupportImage] at hW
  let gB := RationalOrderTransport.Constructions.openFunctionFieldMap (X.componentSupportSchemeIso C B).hom g
  have hgB : gB ≠ 0 := (map_ne_zero_iff _ (RationalOrderTransport.Constructions.openFunctionFieldMap
    (X.componentSupportSchemeIso C B).hom).hom.injective).mpr hg
  apply (X.componentBettiEquiv (ModuleCat.of ℚ ℚ) (p + p)).injective
  funext D
  rw [X.componentBettiEquiv_geometricCycleClassMap, map_zero, Pi.zero_apply]
  by_cases hDC : D = C
  · subst D
    apply integralPrincipalDivisor_geometricClass_zero (X.componentVariety C) B p hW gB hgB
    intro Z
    rw [X.componentDimensionCycleEquiv_apply, hd]
    exact DivisorDescent.Constructions.PrincipalComponentRestriction.principalDivisorCoefficient_componentImage X C B g Z.val
  · have hz : X.componentDimensionCycleEquiv p d D = 0 := by
      ext Z
      rw [X.componentDimensionCycleEquiv_apply, hd, Finsupp.zero_apply]
      apply DivisorDescent.Constructions.principalDivisorCoefficient_other_component X
        (X.componentSupportImage C B) g D
      rw [X.supportComponent_image]
      exact hDC
    rw [hz, map_zero]

theorem isPrincipalDivisor_geometricClass_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (d : X.RationalDimensionCycle p) (hd : IntersectionGeometry.IsPrincipalDivisor X p d) :
    X.geometricCycleClassMap p d = 0 := by
  obtain ⟨W, hW, g, hg, hd⟩ := hd
  exact principalDivisor_geometricClass_zero X p W hW g hg d hd

theorem rationalEquivalences_le_geometricClass_ker (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    IntersectionGeometry.rationalEquivalences X p ≤ LinearMap.ker (X.geometricCycleClassMap p) := by
  apply Submodule.span_le.mpr
  intro d hd
  exact isPrincipalDivisor_geometricClass_zero X p d hd

theorem geometricClass_eq_of_rationallyEquivalent (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    {a b : X.RationalDimensionCycle p} (h : IntersectionGeometry.RationallyEquivalent X p a b) :
    X.geometricCycleClassMap p a = X.geometricCycleClassMap p b := by
  have hz := rationalEquivalences_le_geometricClass_ker X p h
  change X.geometricCycleClassMap p (a - b) = 0 at hz
  rw [map_sub, sub_eq_zero] at hz
  exact hz

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalDescent
