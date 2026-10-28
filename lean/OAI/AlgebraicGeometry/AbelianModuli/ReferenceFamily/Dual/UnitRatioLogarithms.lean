import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitLogarithmicCoefficient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientUnitLogarithms

/-! # Unit Ratio Logarithms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitRatioLogarithms

noncomputable section

/-! Comparing two actual pullbacks of a line-frame unit with the
same reduction gives a normalized unit. Its literal first coefficient
is the logarithmic derivative of their original coefficient difference. -/

variable {B : Type*} [CommRing B]

theorem dualUnitLogCoefficient_inv (u : (DualNumber B)ˣ) :
    UnitLogarithmicCoefficient.dualUnitLogCoefficient u⁻¹ = -UnitLogarithmicCoefficient.dualUnitLogCoefficient u := by
  have h := UnitLogarithmicCoefficient.dualUnitLogCoefficient_mul u u⁻¹
  rw [mul_inv_cancel, UnitLogarithmicCoefficient.dualUnitLogCoefficient_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem dualUnitLogCoefficient_div (u v : (DualNumber B)ˣ) :
    UnitLogarithmicCoefficient.dualUnitLogCoefficient (u / v) = UnitLogarithmicCoefficient.dualUnitLogCoefficient u - UnitLogarithmicCoefficient.dualUnitLogCoefficient v := by
  rw [div_eq_mul_inv, UnitLogarithmicCoefficient.dualUnitLogCoefficient_mul, dualUnitLogCoefficient_inv, sub_eq_add_neg]

theorem dualUnitRatio_fst (u v : (DualNumber B)ˣ) (h : u.val.fst = v.val.fst) :
    (u / v).val.fst = 1 := by
  change u.val.fst * (v⁻¹).val.fst = 1
  rw [h]
  exact UnitLogarithmicCoefficient.dualUnit_fst_mul_inverse v

theorem dualUnitRatio_snd (u v : (DualNumber B)ˣ) (h : u.val.fst = v.val.fst) :
    (u / v).val.snd = UnitLogarithmicCoefficient.dualUnitLogCoefficient u - UnitLogarithmicCoefficient.dualUnitLogCoefficient v :=
  (UnitLogarithmicCoefficient.dualUnitLogCoefficient_normalized (u / v) (dualUnitRatio_fst u v h)).symm.trans
    (dualUnitLogCoefficient_div u v)

variable {k S : Type*} [CommRing k] [CommRing S] [Algebra k S] [Algebra k B] [Algebra S B]

theorem dualUnitPullbackRatio_coefficient (f g : S →+* DualNumber B)
    (hf : ∀ a, (f a).fst = algebraMap S B a) (hg : ∀ a, (g a).fst = algebraMap S B a)
    (d : Derivation k S B) (hd : ∀ a, (f a).snd - (g a).snd = d a) (u : Sˣ) :
    ((Units.map f.toMonoidHom u) / (Units.map g.toMonoidHom u)).val.snd = CoefficientUnitLogarithms.coefficientUnitLog d u := by
  rw [dualUnitRatio_snd _ _ ((hf u.val).trans (hg u.val).symm)]
  change (f u.val).snd * (f (u⁻¹).val).fst - (g u.val).snd * (g (u⁻¹).val).fst =
    d u.val * algebraMap S B (u⁻¹).val
  rw [hf, hg, ← sub_mul, hd]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitRatioLogarithms
