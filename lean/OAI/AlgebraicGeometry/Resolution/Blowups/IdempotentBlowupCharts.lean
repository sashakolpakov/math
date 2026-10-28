import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Localization
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialTransform
import Mathlib.RingTheory.RingHom.Etale

/-! # Idempotent Blowup Charts -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IdempotentBlowupCharts.Construction

noncomputable section

/-! Actual blowup charts of an idempotent center have unit exceptional parameter and are étale. -/

universe u

variable {R : Type u} [CommRing R]

theorem idempotent_blowupChart_exceptional_unit (I : Ideal R) (hI : IsIdempotentElem I) (a : I) :
    IsUnit (Blowup.Charts.Construction.blowupChartConstants I a a.val) := by
  let c := Blowup.Charts.Construction.blowupChartConstants I a a.val
  have hm := congrArg (Ideal.map (Blowup.Charts.Construction.blowupChartConstants I a)) hI.eq
  rw [Ideal.map_mul, ExceptionalIdeal.Construction.blowupChart_extendedIdeal] at hm
  have hc := ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular (Ideal.span {c}) c (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a)
  rw [hm] at hc
  have ht : (Ideal.span {c}).colon (Ideal.span {c} : Set (Blowup.Charts.Construction.blowupChart I a)) = ⊤ :=
    (Submodule.colon_eq_top_iff_subset (N := Ideal.span {c}) _).mpr (Set.Subset.refl _)
  rw [ht] at hc
  exact (Ideal.span_singleton_eq_top).mp hc.symm

def idempotentBlowupChartLocalizationEquiv (I : Ideal R) (hI : IsIdempotentElem I) (a : I) :
    Blowup.Charts.Construction.blowupChart I a ≃ₐ[Blowup.Charts.Construction.blowupChart I a] Localization.Away a.val :=
  IsLocalization.atUnit (Blowup.Charts.Construction.blowupChart I a) (Localization.Away a.val)
    (Blowup.Charts.Construction.blowupChartConstants I a a.val) (idempotent_blowupChart_exceptional_unit I hI a)

theorem idempotentBlowupChartLocalizationEquiv_constants (I : Ideal R) (hI : IsIdempotentElem I)
    (a : I) (r : R) :
    idempotentBlowupChartLocalizationEquiv I hI a (Blowup.Charts.Construction.blowupChartConstants I a r) =
      algebraMap R (Localization.Away a.val) r := by
  have h := (idempotentBlowupChartLocalizationEquiv I hI a).commutes (Blowup.Charts.Construction.blowupChartConstants I a r)
  change idempotentBlowupChartLocalizationEquiv I hI a (Blowup.Charts.Construction.blowupChartConstants I a r) =
    Blowup.Charts.Construction.blowupChartToLocalization I a (Blowup.Charts.Construction.blowupChartConstants I a r) at h
  exact h.trans (Blowup.Charts.Construction.blowupChartToLocalization_constants I a r)

theorem idempotent_blowupChartConstants_etale (I : Ideal R) (hI : IsIdempotentElem I) (a : I) :
    (Blowup.Charts.Construction.blowupChartConstants I a).Etale := by
  let e := idempotentBlowupChartLocalizationEquiv I hI a
  have hfactor : Blowup.Charts.Construction.blowupChartConstants I a = e.symm.toRingHom.comp (algebraMap R (Localization.Away a.val)) := by
    apply RingHom.ext
    intro r
    apply e.injective
    change e (Blowup.Charts.Construction.blowupChartConstants I a r) = e (e.symm (algebraMap R (Localization.Away a.val) r))
    rw [e.apply_symm_apply]
    exact idempotentBlowupChartLocalizationEquiv_constants I hI a r
  rw [hfactor]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale R (Localization.Away a.val)))
    (RingHom.Etale.of_bijective e.symm.bijective)

theorem idempotent_blowupChart_extendedIdeal (I : Ideal R) (hI : IsIdempotentElem I) (a : I) :
    I.map (Blowup.Charts.Construction.blowupChartConstants I a) = ⊤ := by
  rw [ExceptionalIdeal.Construction.blowupChart_extendedIdeal, Ideal.span_singleton_eq_top]
  exact idempotent_blowupChart_exceptional_unit I hI a

theorem idempotent_blowup_controlledTransform (I J : Ideal R) (hI : IsIdempotentElem I)
    (a : I) (b : ℕ) : ControlledTransform.Construction.blowupControlledTransform I J b a = J.map (Blowup.Charts.Construction.blowupChartConstants I a) :=
  Boundary.MonomialTransform.Construction.blowupControlledTransform_of_unit_exceptional I J a b (idempotent_blowupChart_exceptional_unit I hI a)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IdempotentBlowupCharts.Construction
