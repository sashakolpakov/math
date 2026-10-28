import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.CoefficientFieldPoint
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.TypeIntegerFactorization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ArithmeticCoefficientLocalization

/-! # Coefficient Specialization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual principal coefficient parameter specializes to a
localized ring of integers in a finite extension, retaining the chosen
coefficient as a unit and the exact original arithmetic base map. -/

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}

theorem Base.ArithmeticBaseExtension.coefficient_parameter_integral_specialization (B : Base.ArithmeticBaseExtension K κ)
    [Algebra B.R ℂ] (hAlg : algebraMap B.R ℂ = B.embedding.comp B.toField)
    (s : Finset ℂ) (r : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s) (hr : r ≠ 0) (N₀ : ℕ) (hN₀ : N₀ ≠ 0) :
    ∃ D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding,
      N₀ ∣ D.denominator ∧ ∃ ψ : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s →+* D.R,
        IsUnit (ψ r) ∧ (D.toField.comp ψ).comp (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s)) =
          (algebraMap B.extension.carrier D.extension.carrier).comp B.toField := by
  obtain ⟨D, _, j, hjr, hj⟩ := Base.ArithmeticBaseExtension.coefficient_parameter_field_point B hAlg s r hr N₀ hN₀
  have : Algebra.FiniteType ℤ (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s) := Base.ArithmeticBaseExtension.coefficientRing_finiteType_int B s
  obtain ⟨N, hN, hdiv, ψ, hψ, hunit⟩ := Finite.TypeIntegerFactorization.finiteType_ringHom_unit_factors_through_integers j r hjr N₀ hN₀
  let D' := D.withDenominator N hN
  refine ⟨D', hdiv, ψ, hunit, ?_⟩
  exact (congrArg (fun f => f.comp (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s))) hψ).trans hj

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
