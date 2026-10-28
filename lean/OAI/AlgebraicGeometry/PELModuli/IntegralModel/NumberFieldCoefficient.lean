import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.CoefficientFiniteType
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.TypeIntegerFactorization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ArithmeticCoefficientLocalization

/-! # Number Field Coefficient -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Finite coefficients in the already specified generic number field
extend over an enlarged denominator, preserving their exact field values. -/

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}

theorem Base.ArithmeticBaseExtension.generic_coefficients_extend_over_integers (B : Base.ArithmeticBaseExtension K κ)
    [Algebra B.R B.extension.carrier] (hAlg : algebraMap B.R B.extension.carrier = B.toField)
    (s : Finset B.extension.carrier) (N₀ : ℕ) (hN₀ : N₀ ≠ 0) :
    ∃ (N : ℕ) (hN : N ≠ 0), N₀ ∣ N ∧
      ∃ ψ : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R B.extension.carrier s →+* (B.withDenominator N hN).R,
        (B.withDenominator N hN).toField.comp ψ =
          algebraMap (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R B.extension.carrier s) B.extension.carrier ∧
        (B.withDenominator N hN).toField.comp
          (ψ.comp (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R B.extension.carrier s))) = B.toField := by
  have : Algebra.FiniteType ℤ (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R B.extension.carrier s) := Base.ArithmeticBaseExtension.coefficientRing_finiteType_int B s
  obtain ⟨N, hN, hdiv, ψ, hψ⟩ := Finite.TypeIntegerFactorization.finiteType_ringHom_factors_through_integers
    (algebraMap (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R B.extension.carrier s) B.extension.carrier) N₀ hN₀
  refine ⟨N, hN, hdiv, ψ, hψ, ?_⟩
  have h := congrArg (fun f => f.comp (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R B.extension.carrier s))) hψ
  have ht : (algebraMap (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R B.extension.carrier s) B.extension.carrier).comp
      (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R B.extension.carrier s)) = algebraMap B.R B.extension.carrier := rfl
  exact h.trans (ht.trans hAlg)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
