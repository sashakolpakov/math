import Mathlib

/-! # Normalized Valuation Equality -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.NormalizedValuationEquality.Realization

noncomputable section

/-! Equivalent integer-valued valuations with uniformizers are equal. -/

open scoped Classical
open WithZero

theorem mulInt_lt_one_le_uniformizer (z : ℤᵐ⁰) (hz : z < 1) : z ≤ exp (-1 : ℤ) := by
  induction z using WithZero.expRecOn with
  | zero => exact zero_le
  | exp a =>
      rw [← exp_zero, exp_lt_exp] at hz
      rw [exp_le_exp]
      omega

theorem normalized_discrete_valuations_equal {K : Type*} [Field K]
    (v w : Valuation K ℤᵐ⁰) (he : v.IsEquiv w)
    (u t : K) (hu : v u = exp (-1 : ℤ)) (ht : w t = exp (-1 : ℤ)) : v = w := by
  have hlt : exp (-1 : ℤ) < (1 : ℤᵐ⁰) := by
    rw [← exp_zero, exp_lt_exp]
    norm_num
  have hwule : w u ≤ exp (-1 : ℤ) :=
    mulInt_lt_one_le_uniformizer _ (he.lt_one_iff_lt_one.mp (hu.trans_lt hlt))
  have hvtle : v t ≤ exp (-1 : ℤ) :=
    mulInt_lt_one_le_uniformizer _ (he.lt_one_iff_lt_one.mpr (ht.trans_lt hlt))
  have hwu : w u = exp (-1 : ℤ) := le_antisymm hwule (by
    rw [← ht]
    apply (he t u).mp
    rw [hu]
    exact hvtle)
  apply Valuation.ext
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have hvx : v x ≠ 0 := (v.ne_zero_iff).mpr hx
  let n : ℤ := log (v x)
  have hvx' : v x = exp n := (exp_log hvx).symm
  have hv : v (x * u ^ n) = 1 := by
    rw [map_mul, map_zpow₀, hu, hvx', ← exp_zsmul, ← exp_add]
    simp
  have hw : w (x * u ^ n) = 1 := he.eq_one_iff_eq_one.mp hv
  rw [map_mul, map_zpow₀, hu] at hv
  rw [map_mul, map_zpow₀, hwu] at hw
  exact mul_right_cancel₀ (zpow_ne_zero n (show exp (-1 : ℤ) ≠ 0 from WithZero.coe_ne_zero))
    (hv.trans hw.symm)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.NormalizedValuationEquality.Realization
