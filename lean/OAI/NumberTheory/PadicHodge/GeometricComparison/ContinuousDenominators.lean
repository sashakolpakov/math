import Mathlib

/-! # Continuous Denominators -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.ContinuousDenominators.PadicContinuousDenominators

/-! Continuous rational p-adic functions on a compact space have one common integral denominator. -/

theorem exists_denominator (p : ℕ) [Fact p.Prime]
    {X : Type*} [TopologicalSpace X] [CompactSpace X] (f : C(X, ℚ_[p])) :
    ∃ N : ℕ, ∃ g : C(X, ℤ_[p]), ∀ x : X, (p : ℚ_[p]) ^ N * f x = (g x : ℚ_[p]) := by
  obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt p
    (show (0 : ℝ) < 1 / (‖f‖ + 1) by positivity)
  have hb : (p : ℝ) ^ (-(N : ℤ)) * (‖f‖ + 1) < 1 :=
    (lt_div_iff₀ (by positivity)).mp hN
  have hx (x : X) : ‖(p : ℚ_[p]) ^ N * f x‖ ≤ 1 := by
    rw [norm_mul, Padic.norm_p_pow]
    exact (mul_le_mul_of_nonneg_left
      ((f.norm_coe_le_norm x).trans (le_add_of_nonneg_right zero_le_one))
      (by positivity)).trans hb.le
  exact ⟨N, ⟨fun x => ⟨(p : ℚ_[p]) ^ N * f x, hx x⟩,
    (continuous_const.mul f.continuous).subtype_mk hx⟩, fun _ => rfl⟩

end NumberTheory.PadicHodge.GeometricComparison.ContinuousDenominators.PadicContinuousDenominators

namespace NumberTheory.PadicHodge.GeometricComparison.ContinuousDenominators.PadicIntegerLocalization

/-! The rational p-adic field is obtained by inverting p in the actual p-adic integers. -/

variable (p : ℕ) [Fact p.Prime]

instance localized : IsLocalization.Away (p : ℤ_[p]) ℚ_[p] := by
  apply IsLocalization.Away.mk (p : ℤ_[p])
  · apply isUnit_iff_ne_zero.mpr
    change (p : ℚ_[p]) ≠ 0
    exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  · intro z
    obtain ⟨N, g, hg⟩ := PadicContinuousDenominators.exists_denominator p
      (ContinuousMap.const PUnit.{1} z)
    exact ⟨N, g PUnit.unit, (mul_comm z ((p : ℚ_[p]) ^ N)).trans (hg PUnit.unit)⟩
  · intro a b h
    have he : a = b := Subtype.ext h
    exact ⟨0, by rw [he]⟩

end NumberTheory.PadicHodge.GeometricComparison.ContinuousDenominators.PadicIntegerLocalization

end

end OAI
