import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ArithmeticCoefficientLocalization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.BaseChange

/-! # Localization Maps -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! A compatible map between arithmetic localizations is an actual open
immersion on spectra and preserves the prescribed integral CM embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.NumberField

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ) (D : ℕ) (hD : D ≠ 0)
    (φ : B.R →+* (B.withDenominator D hD).R)
    (hφ : (B.withDenominator D hD).toField.comp φ = B.toField)

include hφ

theorem Base.ArithmeticBaseExtension.coefficient_map_algebraMap :
    φ.comp (algebraMap (𝓞 B.extension.carrier) B.R) =
      algebraMap (𝓞 B.extension.carrier) (B.withDenominator D hD).R := by
  apply RingHom.ext
  intro a
  apply (B.withDenominator D hD).toField_injective
  exact (RingHom.congr_fun hφ (algebraMap (𝓞 B.extension.carrier) B.R a)).trans
    ((ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap B.extension.carrier B.denominator B.denominator_ne_zero a).trans
      (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap B.extension.carrier D hD a).symm)

theorem Base.ArithmeticBaseExtension.coefficient_map_isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) := by
  let a := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 B.extension.carrier) B.R))
  let a' := Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 B.extension.carrier) (B.withDenominator D hD).R))
  have ha : IsOpenImmersion a := inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 B.extension.carrier) B.R))))
  have ha' : IsOpenImmersion a' := inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 B.extension.carrier) (B.withDenominator D hD).R))))
  have he : Spec.map (CommRingCat.ofHom φ) ≫ a = a' := by
    rw [← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (Base.ArithmeticBaseExtension.coefficient_map_algebraMap B D hD φ hφ)
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ) ≫ a) := he.symm ▸ ha'
  exact IsOpenImmersion.of_comp (Spec.map (CommRingCat.ofHom φ)) a

theorem Base.ArithmeticBaseExtension.coefficient_map_integralEmbedding {E : Type} [Field E] (iota : E →+* K) :
    φ.comp (B.integralEmbedding iota) = (B.withDenominator D hD).integralEmbedding iota := by
  apply RingHom.ext
  intro a
  apply (B.withDenominator D hD).toField_injective
  exact (RingHom.congr_fun hφ (B.integralEmbedding iota a)).trans
    ((B.integralEmbedding_toField iota a).trans
      ((B.withDenominator D hD).integralEmbedding_toField iota a).symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
