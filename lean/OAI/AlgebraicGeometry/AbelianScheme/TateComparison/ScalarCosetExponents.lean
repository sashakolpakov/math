import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitCosetComponents

/-! # Scalar Coset Exponents -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ScalarCosetExponents

noncomputable section

/-! Powers of q give distinct scalar cosets modulo integral units.
Thus an actual terminal scalar coset determines its multiplier. -/

variable (q : ℕ) [Fact q.Prime]

theorem qUnit_zpow_mem_scalarLevel_iff (n : ℤ) :
    HeckeKernel.qUnit q ^ n ∈ SplitCosetComponents.scalarIntegralLevel q ↔ n = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    have hn := congrArg (fun a : ℚ_[q]ˣ => ‖(a : ℚ_[q])‖) hu
    simp only [Units.coe_map, Units.val_zpow_eq_zpow_val, HeckeKernel.qUnit, Units.val_mk0] at hn
    change ‖(u.val : ℚ_[q])‖ = ‖(q : ℚ_[q]) ^ n‖ at hn
    rw [← PadicInt.norm_def, PadicInt.norm_units, Padic.norm_p_zpow] at hn
    have hp : 0 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
    have hp1 : (q : ℝ) ≠ 1 := by exact_mod_cast (Fact.out : q.Prime).ne_one
    have he : -(n : ℤ) = 0 := zpow_right_injective₀ hp hp1 (hn.symm.trans (zpow_zero (q : ℝ)).symm)
    exact neg_eq_zero.mp he
  · rintro rfl
    simpa only [zpow_zero] using (SplitCosetComponents.scalarIntegralLevel q).one_mem

theorem scalarCoset_qUnit_zpow_injective :
    Function.Injective (fun n : ℤ => (QuotientGroup.mk (HeckeKernel.qUnit q ^ n) : ℚ_[q]ˣ ⧸ SplitCosetComponents.scalarIntegralLevel q)) := by
  intro a b h
  have he := QuotientGroup.leftRel_apply.mp (Quotient.exact h)
  have hx : (HeckeKernel.qUnit q) ^ (b - a) ∈ SplitCosetComponents.scalarIntegralLevel q := by
    simpa only [zpow_sub, div_eq_mul_inv, mul_comm] using he
  have hn := (qUnit_zpow_mem_scalarLevel_iff q (b - a)).mp hx
  exact (sub_eq_zero.mp hn).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ScalarCosetExponents
