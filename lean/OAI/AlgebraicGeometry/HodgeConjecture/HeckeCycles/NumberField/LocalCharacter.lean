import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.AdelicCharacter
import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteCharacterProduct
import OAI.RepresentationTheory.Weil.AdelicSplitting.UnramifiedCharacter

/-! # Local Character -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.LocalCharacter.CM

noncomputable section

/-! The actual finite character is the finite product of its local
characters. Its normalization agrees with the constructed trace character. -/

open scoped Classical _root_.NumberField
open Filter Function

variable (F : Type) [Field F] [NumberField F]
  (ψ : AddChar (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)

include hc hu in
theorem finite_support (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) : HasFiniteMulSupport
    (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v) (a v)) := by
  have h := RepresentationTheory.Weil.AdelicSplitting.UnramifiedCharacter.Construction.localAdditiveCharacter_unramified_finite F ψ hu hc
  filter_upwards [h, a.property] with v hv ha
  exact hv (a v) ha

include hc hu in
theorem finite_product (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v) (a v)) =
      RepresentationTheory.Weil.AdelicSplitting.FiniteCharacterProduct.Construction.finiteAdelicCharacter F ψ a := by
  rw [← tprod_eq_finprod (L := SummationFilter.unconditional _) (finite_support F ψ hc hu a)]
  exact (RepresentationTheory.Weil.AdelicSplitting.FiniteCharacterProduct.Construction.localAdditiveCharacter_finite_hasProd F ψ hc a).tprod_eq

theorem constructed_finite (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    RepresentationTheory.Weil.AdelicSplitting.FiniteCharacterProduct.Construction.finiteAdelicCharacter F (AdelicCharacter.CM.character F) a =
      FiniteCharacter.CM.character F a := by
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.trace F 0) *
    FiniteCharacter.CM.character F a = _
  rw [map_zero, AddChar.map_zero_eq_one, one_mul]

theorem constructed_product (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F (AdelicCharacter.CM.character F) (.inr v) (a v)) =
        FiniteCharacter.CM.character F a :=
  (finite_product F (AdelicCharacter.CM.character F)
    (AdelicCharacter.CM.character_continuous F)
    (AdelicCharacter.CM.character_unitary F) a).trans (constructed_finite F a)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.LocalCharacter.CM
