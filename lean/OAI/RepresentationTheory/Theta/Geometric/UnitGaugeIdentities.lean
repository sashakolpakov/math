import Mathlib.Algebra.Group.Basic

/-! # Unit Gauge Identities -/

namespace OAI.RepresentationTheory.Theta.Geometric.UnitGaugeIdentities

/-! Exact gauge identities in the unit group, including first-order
automorphy, without any field-only cancellation. -/

theorem unitGauge_independent {G : Type*} [CommGroup G]
    (r r' s s' t t' : G) (h : r * (s' / s) = (t' / t) * r') :
    r * t / s = r' * t' / s' := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    congrArg (fun x => x * (t / s')) h

theorem unitGauge_automorphy {G : Type*} [CommGroup G]
    (r s t j δ : G) : (r * (j * t) / ((j * δ) * s)) * δ = r * t / s := by
  have h : r * (j * t) = j * (r * t) := by ac_rfl
  rw [h, mul_assoc j δ s, mul_div_mul_left_eq_div]
  simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

end OAI.RepresentationTheory.Theta.Geometric.UnitGaugeIdentities
