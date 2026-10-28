import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Derivation

/-! # Unit Logarithmic Coefficient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitLogarithmicCoefficient

noncomputable section

/-! Logarithmic first-order coefficients of arbitrary dual-number
units. A deformed transition contributes the logarithmic derivative
of the reduced unit to the actual triangle equation. -/

variable {R S : Type*} [CommRing R] [CommRing S]

def dualUnitLogCoefficient (u : (DualNumber R)ˣ) : R := u.val.snd * (u⁻¹).val.fst

theorem dualUnit_fst_mul_inverse (u : (DualNumber R)ˣ) :
    u.val.fst * (u⁻¹).val.fst = 1 := congrArg TrivSqZeroExt.fst u.val_inv

theorem dualUnitLogCoefficient_one : dualUnitLogCoefficient (1 : (DualNumber R)ˣ) = 0 := zero_mul 1

theorem dualUnitLogCoefficient_mul (u v : (DualNumber R)ˣ) :
    dualUnitLogCoefficient (u * v) = dualUnitLogCoefficient u + dualUnitLogCoefficient v := by
  unfold dualUnitLogCoefficient
  rw [mul_inv_rev]
  change (u.val.fst * v.val.snd + u.val.snd * v.val.fst) * ((v⁻¹).val.fst * (u⁻¹).val.fst) = _
  calc
    _ = v.val.snd * (u.val.fst * (u⁻¹).val.fst) * (v⁻¹).val.fst +
        u.val.snd * (v.val.fst * (v⁻¹).val.fst) * (u⁻¹).val.fst := by ring
    _ = _ := by rw [dualUnit_fst_mul_inverse, dualUnit_fst_mul_inverse, mul_one, mul_one, add_comm]

theorem dualUnitLogCoefficient_normalized (u : (DualNumber R)ˣ) (hu : u.val.fst = 1) :
    dualUnitLogCoefficient u = u.val.snd := by
  unfold dualUnitLogCoefficient
  rw [UnitCoordinates.dualUnit_fst_inv u hu, mul_one]

theorem dualUnitLogCoefficient_map (f : R →+* S) (u : (DualNumber R)ˣ) :
    dualUnitLogCoefficient (Units.map (NumberCoefficients.dualNumberRingMap f).toMonoidHom u) = f (dualUnitLogCoefficient u) := by
  change f u.val.snd * f (u⁻¹).val.fst = f (u.val.snd * (u⁻¹).val.fst)
  exact (map_mul f _ _).symm

variable {k : Type*} [CommRing k] [Algebra k R]

theorem dualUnitLogCoefficient_derivation (d : Derivation k R R) (u : (DualNumber R)ˣ) :
    dualUnitLogCoefficient (Units.map (Dual.Derivation.dualDerivationAutomorphism d).toAlgHom.toMonoidHom u) =
      dualUnitLogCoefficient u + d u.val.fst * (u⁻¹).val.fst := by
  change (d u.val.fst + u.val.snd) * (u⁻¹).val.fst =
    u.val.snd * (u⁻¹).val.fst + d u.val.fst * (u⁻¹).val.fst
  ring

theorem dualUnitLogCoefficient_twisted_triangle (d : Derivation k R R)
    (u v w : (DualNumber R)ˣ)
    (h : w = u * Units.map (Dual.Derivation.dualDerivationAutomorphism d).toAlgHom.toMonoidHom v) :
    dualUnitLogCoefficient w - dualUnitLogCoefficient u - dualUnitLogCoefficient v =
      d v.val.fst * (v⁻¹).val.fst := by
  rw [h, dualUnitLogCoefficient_mul, dualUnitLogCoefficient_derivation]
  abel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitLogarithmicCoefficient
