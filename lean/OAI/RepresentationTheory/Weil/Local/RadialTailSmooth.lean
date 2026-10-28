import OAI.RepresentationTheory.Weil.Local.RadialTailCutoffBound

/-! # Radial Tail Smooth -/

namespace OAI.RepresentationTheory.Weil.Local.RadialTailSmooth.Construction

noncomputable section

/-! Smoothness of the radial tail weight across its zero neighborhood. -/

open Filter Set
open scoped _root_.Topology ContDiff

theorem radialCutoff_contDiff (R : ℝ) : ContDiff ℝ ∞ (RadialTailCutoffBound.Construction.radialCutoff R) :=
  RadialTailCutoffBound.Construction.radialCutoffBase_contDiff.comp (contDiff_id.div_const R)

theorem radialTailWeight_contDiff (s ε R : ℝ) (hR : 0 < R) :
    ContDiff ℝ ∞ (RadialTailCutoffBound.Construction.radialTailWeight s ε R) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : 0 < t
  · have hp : ContDiffAt ℝ ∞ (fun x : ℝ => x ^ s) t := Real.contDiffAt_rpow_const_of_ne ht.ne'
    have he : ContDiffAt ℝ ∞ (fun x : ℝ => Real.exp (-ε * x ^ s)) t :=
      Real.contDiff_exp.contDiffAt.comp t (contDiffAt_const.mul hp)
    have hw : ContDiffAt ℝ ∞ (RealPower.Construction.realPowerWeight s ε) t := he.div contDiffAt_id ht.ne'
    exact (radialCutoff_contDiff R).contDiffAt.mul hw
  · have htR : t < R := (le_of_not_gt ht).trans_lt hR
    have heq : RadialTailCutoffBound.Construction.radialTailWeight s ε R =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds htR] with x hx
      exact RadialTailCutoffBound.Construction.radialTailWeight_zero s ε R x hR hx
    exact contDiffAt_const.congr_of_eventuallyEq heq

theorem radialTailWeight_deriv (s ε R : ℝ) (hR : 0 < R) :
    deriv (RadialTailCutoffBound.Construction.radialTailWeight s ε R) = RadialTailCutoffBound.Construction.radialTailWeightDerivative s ε R :=
  funext fun t => (RadialTailCutoffBound.Construction.radialTailWeight_hasDerivAt s ε R hR t).deriv

theorem radialTailWeight_second_deriv (s ε R : ℝ) (hR : 0 < R) :
    deriv (deriv (RadialTailCutoffBound.Construction.radialTailWeight s ε R)) = RadialTailCutoffBound.Construction.radialTailWeightSecondDerivative s ε R := by
  rw [radialTailWeight_deriv s ε R hR]
  exact funext fun t => (RadialTailCutoffBound.Construction.radialTailWeightDerivative_hasDerivAt s ε R hR t).deriv

theorem radialTailWeightDerivative_contDiff (s ε R : ℝ) (hR : 0 < R) :
    ContDiff ℝ ∞ (RadialTailCutoffBound.Construction.radialTailWeightDerivative s ε R) := by
  rw [← radialTailWeight_deriv s ε R hR]
  exact (radialTailWeight_contDiff s ε R hR).iterate_deriv 1

theorem radialTailWeightSecondDerivative_contDiff (s ε R : ℝ) (hR : 0 < R) :
    ContDiff ℝ ∞ (RadialTailCutoffBound.Construction.radialTailWeightSecondDerivative s ε R) := by
  rw [← radialTailWeight_second_deriv s ε R hR]
  exact (radialTailWeight_contDiff s ε R hR).iterate_deriv 2

end

end OAI.RepresentationTheory.Weil.Local.RadialTailSmooth.Construction
