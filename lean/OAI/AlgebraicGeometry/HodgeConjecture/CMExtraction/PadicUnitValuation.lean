import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Iwasawa

/-! # Padic Unit Valuation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicUnitValuation.Iwasawa

noncomputable section

/-! Split a nonzero p-adic scalar into its exact prime power and an
actual p-adic integer unit, retaining the original inclusion. -/

variable (q : ℕ) [Fact q.Prime]

theorem padic_unit_valuation_factorization (a : ℚ_[q]ˣ) :
    ∃ u : ℤ_[q]ˣ, a = AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ a.val.valuation *
      Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom u := by
  have hq : (q : ℚ_[q]) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  let b : ℚ_[q] := a.val / (q : ℚ_[q]) ^ a.val.valuation
  have hpow : ‖(q : ℚ_[q]) ^ a.val.valuation‖ = ‖a.val‖ := by
    rw [Padic.norm_eq_zpow_neg_valuation (zpow_ne_zero _ hq), Padic.valuation_zpow,
      Padic.valuation_p, mul_one, Padic.norm_eq_zpow_neg_valuation a.ne_zero]
  have hn : ‖b‖ = 1 := by
    dsimp [b]
    rw [norm_div, hpow, div_self (norm_ne_zero_iff.mpr a.ne_zero)]
  let u₀ : ℤ_[q] := ⟨b, hn.le⟩
  have hu : IsUnit u₀ := PadicInt.isUnit_iff.mpr hn
  refine ⟨hu.unit, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
  change a.val = (q : ℚ_[q]) ^ a.val.valuation *
    (PadicInt.Coe.ringHom (p := q)) hu.unit.val
  rw [hu.unit_spec]
  change a.val = (q : ℚ_[q]) ^ a.val.valuation * (a.val / (q : ℚ_[q]) ^ a.val.valuation)
  field_simp

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicUnitValuation.Iwasawa
