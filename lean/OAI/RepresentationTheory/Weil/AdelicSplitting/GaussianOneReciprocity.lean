import OAI.RepresentationTheory.Weil.AdelicSplitting.FresnelOperators
import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaFourierPositive
import OAI.RepresentationTheory.Weil.AdelicSplitting.PositiveScalarProduct

/-! # Gaussian One Reciprocity -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.GaussianOneReciprocity.Construction

noncomputable section

/-! Gaussian reciprocity for the standard scalar quadratic form, obtained
from actual Fourier-quadratic words and adelic Poisson positivity. -/

open scoped Classical
open _root_.MeasureTheory

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
variable (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1)
variable (hn : ∀ v : ArchimedeanAdeles.Construction.Places F, ∃ t : ArchimedeanAdeles.Construction.Completion F v, Characters.Construction.localAdditiveCharacter F ψ v t ≠ 1)
variable (hμ : ∀ v : ArchimedeanAdeles.Construction.Places F,
  (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure)

include hp in
theorem rationalQuadratic_mem_positiveThetaSubgroup (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N) :
    QuadraticGenerators.Construction.rationalQuadraticFamily F N ψ hu hc B ∈ TestFamilyAction.Construction.positiveThetaSubgroup F N ψ := by
  intro f
  refine ⟨1, zero_lt_one, ?_⟩
  simpa only [Complex.ofReal_one, one_mul] using f.theta_rational_quadratic F N ψ hc hp B
    (QuadraticGenerators.Construction.rationalQuadraticFamily F N ψ hu hc B) (QuadraticGenerators.Construction.rationalQuadraticFamily_spec F N ψ hu hc B)

include hp hμ in
theorem gaussianPowerCircle_principal_hasProd (a : Rational.Construction.RestrictedCover F N ψ)
    (ha : Rational.Construction.IsRationalFourier F N ψ a) :
    HasProd (FresnelOperators.Construction.gaussianPowerCircle F N ψ hc hu hn) 1 := by
  let A := FresnelOperators.Construction.fresnelFirstWord F N ψ hc hu a
  let B := FresnelOperators.Construction.fresnelSecondWord F N ψ hc hu a
  let s := A * B⁻¹
  let P := TestFamilyAction.Construction.positiveThetaSubgroup F N ψ
  have hW : a ∈ P := ThetaFourierPositive.Construction.rationalFourier_mem_positiveThetaSubgroup F N ψ hc hu hp
    (fun v => hn (.inl v)) (fun v => hμ (.inr v)) (fun v => hμ (.inl v)) a ha
  have hQ : FresnelOperators.Construction.unitQuadraticFamily F N ψ hc hu ∈ P :=
    rationalQuadratic_mem_positiveThetaSubgroup F N ψ hc hu hp (FresnelAlgebra.Construction.unitSymmetricMatrix F N)
  have hQm : FresnelOperators.Construction.negativeUnitQuadraticFamily F N ψ hc hu ∈ P :=
    rationalQuadratic_mem_positiveThetaSubgroup F N ψ hc hu hp (FresnelAlgebra.Construction.negativeUnitSymmetricMatrix F N)
  have hA : A ∈ P := P.mul_mem (P.mul_mem hW hQ) hW
  have hB : B ∈ P := P.mul_mem (P.mul_mem hQm hW) hQm
  have hs : s ∈ P := P.mul_mem hA (P.inv_mem hB)
  apply PositiveScalarProduct.Construction.restricted_scalar_positive_hasProd_one F N ψ s hs (FresnelOperators.Construction.gaussianPowerCircle F N ψ hc hu hn)
  intro v
  change FresnelOperators.Construction.fresnelFirstWord F N ψ hc hu a v * (FresnelOperators.Construction.fresnelSecondWord F N ψ hc hu a v)⁻¹ = _
  rw [FresnelOperators.Construction.fresnel_words_scalar F N ψ hc hu hn a ha v, mul_inv_cancel_right]

include hc hu hp hn hμ in
theorem gaussianIndex_one_power_principal_hasProd (a : Rational.Construction.RestrictedCover F N ψ)
    (ha : Rational.Construction.IsRationalFourier F N ψ a) :
    HasProd (fun v : ArchimedeanAdeles.Construction.Places F => Local.FunctionsMetaplectic.Construction.gaussianIndex (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F ψ v) 1 ^ N) 1 := by
  have h := (gaussianPowerCircle_principal_hasProd F N ψ hc hu hp hn hμ a ha).map
    Circle.coeHom continuous_subtype_val
  exact h

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.GaussianOneReciprocity.Construction
