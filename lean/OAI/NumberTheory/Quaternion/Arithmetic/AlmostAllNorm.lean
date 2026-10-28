import OAI.NumberTheory.Quaternion.Arithmetic.NormResidueField
import OAI.NumberTheory.Quaternion.Arithmetic.FiniteUnitCoefficients

/-! # Almost All Norm -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AlmostAllNorm

noncomputable section

/-! The norm equation that splits a quaternion algebra is solvable
at all but finitely many finite places of its number field. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Filter

variable {F : Type} [Field F] [NumberField F]

theorem eventually_quaternion_splitting_norm_equation (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∃ x y : v.adicCompletion F,
        x ^ 2 - algebraMap F (v.adicCompletion F) a * y ^ 2 = algebraMap F (v.adicCompletion F) b := by
  have htwo := FiniteUnitCoefficients.eventually_finite_coefficient_norm_one (2 : F) (by norm_num)
  filter_upwards [FiniteUnitCoefficients.eventually_finite_coefficient_norm_one a ha,
    FiniteUnitCoefficients.eventually_finite_coefficient_norm_one b hb, htwo] with v hva hvb hv2
  apply NormResidueField.unit_binary_norm_surjective _ _ hva hvb
  simpa only [map_ofNat] using hv2

end

end OAI.NumberTheory.Quaternion.Arithmetic.AlmostAllNorm
