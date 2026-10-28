import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.TowerEmbedding
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ArithmeticCoefficientLocalization

/-! # Tower Denominator Map -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! A common arithmetic denominator constructs the actual map from
the fixed-field dual model to a further finite-field arithmetic model,
with its exact generic-field value and coefficient-map compatibility. -/

open scoped _root_.NumberField

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ)
    (D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding)

theorem Base.ArithmeticBaseExtension.exists_tower_denominator_map (n : ℕ) (hn : n ≠ 0) (hdiv : n ∣ D.denominator) :
    ∃ ψ : (B.withDenominator n hn).R →+* D.R,
      D.toField.comp ψ = (algebraMap B.extension.carrier D.extension.carrier).comp
        (B.withDenominator n hn).toField := by
  let α := algebraMap B.extension.carrier D.extension.carrier
  let j : 𝓞 B.extension.carrier →+* D.R :=
    (algebraMap (𝓞 D.extension.carrier) D.R).comp (NumberField.RingOfIntegers.mapRingHom α)
  have hu : IsUnit (j (n : 𝓞 B.extension.carrier)) := by
    rw [map_natCast]
    exact D.divisor_isUnit n hdiv
  let ψ : (B.withDenominator n hn).R →+* D.R := IsLocalization.Away.lift (g := j) (n : 𝓞 B.extension.carrier) hu
  refine ⟨ψ, ?_⟩
  apply IsLocalization.ringHom_ext (Submonoid.powers (n : 𝓞 B.extension.carrier))
  ext x
  change D.toField (ψ (algebraMap (𝓞 B.extension.carrier) (B.withDenominator n hn).R x)) =
    α ((B.withDenominator n hn).toField (algebraMap (𝓞 B.extension.carrier) (B.withDenominator n hn).R x))
  rw [IsLocalization.Away.lift_eq]
  change ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField D.extension.carrier D.denominator D.denominator_ne_zero
      (algebraMap (𝓞 D.extension.carrier) D.R (NumberField.RingOfIntegers.mapRingHom α x)) =
    α (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField B.extension.carrier n hn
      (algebraMap (𝓞 B.extension.carrier) (B.withDenominator n hn).R x))
  rw [ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap, ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap]
  rfl

theorem Base.ArithmeticBaseExtension.tower_denominator_map_compatible (n : ℕ) (hn : n ≠ 0)
    (ψ : (B.withDenominator n hn).R →+* D.R)
    (hψ : D.toField.comp ψ = (algebraMap B.extension.carrier D.extension.carrier).comp
      (B.withDenominator n hn).toField)
    (φ₀ : B.R →+* (B.withDenominator n hn).R)
    (hφ₀ : (B.withDenominator n hn).toField.comp φ₀ = B.toField)
    (φ : B.R →+* D.R)
    (hφ : D.toField.comp φ = (algebraMap B.extension.carrier D.extension.carrier).comp B.toField) :
    ψ.comp φ₀ = φ := by
  ext x
  apply D.toField_injective
  exact (RingHom.congr_fun hψ (φ₀ x)).trans
    ((congrArg (algebraMap B.extension.carrier D.extension.carrier) (RingHom.congr_fun hφ₀ x)).trans
      (RingHom.congr_fun hφ x).symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
