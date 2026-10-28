import OAI.RepresentationTheory.Theta.Geometric.Dual.UnitEvaluation
import OAI.RepresentationTheory.Theta.Geometric.UnitGaugeIdentities

/-! # Gauge Covariance -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.GaugeCovariance

noncomputable section

section

/-! Unit-group gauge identities applied to the actual dual-number
coefficients of line-bundle comparisons. -/

theorem dualGauge_independent (r r' s s' t t' : DualNumber ℂ)
    (hr : IsUnit r) (hr' : IsUnit r') (hs : IsUnit s) (hs' : IsUnit s')
    (ht : IsUnit t) (ht' : IsUnit t')
    (h : r * (s' * s⁻¹) = (t' * t⁻¹) * r') :
    r * t * s⁻¹ = r' * t' * s'⁻¹ := by
  have H : hr.unit * (hs'.unit / hs.unit) = (ht'.unit / ht.unit) * hr'.unit := by
    apply Units.ext
    simpa only [div_eq_mul_inv, Units.val_mul, UnitEvaluation.dualUnit_inv_value,
      IsUnit.unit_spec] using h
  have H' := congrArg (fun u : (DualNumber ℂ)ˣ => (u : DualNumber ℂ))
    (UnitGaugeIdentities.unitGauge_independent hr.unit hr'.unit hs.unit hs'.unit ht.unit ht'.unit H)
  simpa only [div_eq_mul_inv, Units.val_mul, UnitEvaluation.dualUnit_inv_value, IsUnit.unit_spec] using H'

theorem dualGauge_automorphy (r s t j δ : DualNumber ℂ)
    (hr : IsUnit r) (hs : IsUnit s) (ht : IsUnit t) (hj : IsUnit j) (hδ : IsUnit δ) :
    (r * (j * t) * ((j * δ) * s)⁻¹) * δ = r * t * s⁻¹ := by
  have H := congrArg (fun u : (DualNumber ℂ)ˣ => (u : DualNumber ℂ))
    (UnitGaugeIdentities.unitGauge_automorphy hr.unit hs.unit ht.unit hj.unit hδ.unit)
  simpa only [div_eq_mul_inv, Units.val_mul, UnitEvaluation.dualUnit_inv_value, IsUnit.unit_spec] using H

end

/-! Covariance of the comparison gauge under separate source and
target unit factors. -/

theorem unitGauge_covariance {G : Type*} [CommGroup G] (r s t j k : G) :
    (r * (j * t) / (k * s)) * k = j * (r * t / s) := by
  simp only [div_eq_mul_inv, mul_inv_rev]
  calc
    (r * (j * t) * (s⁻¹ * k⁻¹)) * k = (j * (r * t * s⁻¹)) * (k⁻¹ * k) := by ac_rfl
    _ = j * (r * t * s⁻¹) := by rw [inv_mul_cancel, mul_one]

theorem dualGauge_covariance (r s t j k : DualNumber ℂ)
    (hr : IsUnit r) (hs : IsUnit s) (ht : IsUnit t) (hj : IsUnit j) (hk : IsUnit k) :
    (r * (j * t) * (k * s)⁻¹) * k = j * (r * t * s⁻¹) := by
  have H := congrArg (fun u : (DualNumber ℂ)ˣ => (u : DualNumber ℂ))
    (unitGauge_covariance hr.unit hs.unit ht.unit hj.unit hk.unit)
  simpa only [div_eq_mul_inv, Units.val_mul, UnitEvaluation.dualUnit_inv_value, IsUnit.unit_spec] using H

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.GaugeCovariance
