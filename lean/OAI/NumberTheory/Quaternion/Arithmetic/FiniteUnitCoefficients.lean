import OAI.NumberTheory.Quaternion.Arithmetic.ScalarApproximation
import OAI.NumberTheory.Quaternion.Arithmetic.LocalCompletion

/-! # Finite Unit Coefficients -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteUnitCoefficients

noncomputable section

/-! Every nonzero number-field scalar is a unit at all but finitely
many finite places, in the actual completion norms. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Filter

variable {F : Type} [Field F] [NumberField F]

theorem eventually_finite_coefficient_norm_one (a : F) (ha : a ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ‖algebraMap F (v.adicCompletion F) a‖ = 1 := by
  have h₁ := (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F) a).property
  have h₂ := (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F) a⁻¹).property
  filter_upwards [h₁, h₂] with v hv₁ hv₂
  have hn₁ : ‖algebraMap F (v.adicCompletion F) a‖ ≤ 1 :=
    (Valued.toNormedField.norm_le_one_iff).mpr hv₁
  have hn₂ : ‖algebraMap F (v.adicCompletion F) a⁻¹‖ ≤ 1 :=
    (Valued.toNormedField.norm_le_one_iff).mpr hv₂
  have he : ‖algebraMap F (v.adicCompletion F) a‖ *
      ‖algebraMap F (v.adicCompletion F) a⁻¹‖ = 1 := by
    rw [← norm_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, norm_one]
  apply le_antisymm hn₁
  calc
    1 = ‖algebraMap F (v.adicCompletion F) a‖ * ‖algebraMap F (v.adicCompletion F) a⁻¹‖ := he.symm
    _ ≤ ‖algebraMap F (v.adicCompletion F) a‖ * 1 :=
      mul_le_mul_of_nonneg_left hn₂ (norm_nonneg _)
    _ = ‖algebraMap F (v.adicCompletion F) a‖ := mul_one _

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteUnitCoefficients
