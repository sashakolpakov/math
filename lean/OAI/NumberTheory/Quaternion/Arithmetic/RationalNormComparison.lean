import OAI.NumberTheory.Quaternion.Arithmetic.PrimeLocalIntegral

/-! # Rational Norm Comparison -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.RationalNormComparison

noncomputable section

/-! Finite places of the same residue characteristic induce the same
ordering of norms on rational scalars, even when their normalizations
differ because of ramification. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

theorem ratCast_norm_le_one_iff (v : HeightOneSpectrum (𝓞 F)) (q : ℚ) :
    ‖(q : v.adicCompletion F)‖ ≤ 1 ↔ ¬ LocalCompletion.residuePrime v ∣ q.den := by
  refine ⟨PrimeLocalIntegral.residuePrime_not_dvd_den_of_ratCast_norm_le_one v q, fun h => ?_⟩
  rw [Rat.cast_def, norm_div, LocalCompletion.natCast_norm_eq_one_of_not_dvd v q.den h, div_one]
  exact PrimeLocalIntegral.intCast_norm_le_one v q.num

theorem ratCast_norm_le_iff_same_residuePrime (v w : HeightOneSpectrum (𝓞 F))
    (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) (q r : ℚ) :
    ‖(q : v.adicCompletion F)‖ ≤ ‖(r : v.adicCompletion F)‖ ↔
      ‖(q : w.adicCompletion F)‖ ≤ ‖(r : w.adicCompletion F)‖ := by
  let : CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F _
  let : CharZero (w.adicCompletion F) := Algebra.charZero_of_charZero F _
  by_cases hr : r = 0
  · subst r
    simp
  have hv : 0 < ‖(r : v.adicCompletion F)‖ := norm_pos_iff.mpr (Rat.cast_ne_zero.mpr hr)
  have hw : 0 < ‖(r : w.adicCompletion F)‖ := norm_pos_iff.mpr (Rat.cast_ne_zero.mpr hr)
  rw [← div_le_one₀ hv, ← div_le_one₀ hw, ← norm_div, ← norm_div,
    ← Rat.cast_div, ← Rat.cast_div, ratCast_norm_le_one_iff, ratCast_norm_le_one_iff, hvw]

end

end OAI.NumberTheory.Quaternion.Arithmetic.RationalNormComparison
