import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.CoefficientModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Isomorphisms
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.CoefficientSpecialization

/-! # Arithmetic Isomorphisms -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.ArithmeticIsomorphisms

noncomputable section

/-! An isomorphism of actual complex fibers yields an isomorphism of the
specified arithmetic schemes after a constructed arithmetic base change. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem fixed_isomorphism_coefficient_descent
    (R K : Type) [CommRing R] [Field K] [Algebra R K]
    (X Y : Over (Spec (.of R)))
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj Y) :
    ∃ s : Finset K, Nonempty ((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X ≅
      (Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj Y) := by
  let MX := CoefficientModels.Coefficients.fixedSourceModel R K ∅ X hX
  let MY := CoefficientModels.Coefficients.fixedSourceModel R K ∅ Y hY
  obtain ⟨s, h, a, _⟩ := Coefficient.Isomorphisms.Coefficients.isomorphism_between_models_descends MX.model MY.model
    MX.finitePresentation MY.finitePresentation MX.specialization MY.specialization
    MX.cartesian MY.cartesian e
  let c (Z : Over (Spec (.of R))) := Group.BaseChangeComparisons.GroupBaseChange.iteratedIso Z
    (CoefficientModels.Coefficients.parameterBaseMap R K ∅) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h) (CoefficientModels.Coefficients.parameterBaseMap R K s)
    (CoefficientModels.Coefficients.coefficient_parameterBaseMap R K h)
  exact ⟨s, ⟨(c X).symm ≪≫ a ≪≫ c Y⟩⟩

theorem arithmetic_fixed_isomorphism_exists
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ) [Algebra B.R ℂ]
    (hAlg : algebraMap B.R ℂ = B.embedding.comp B.toField)
    (X Y : Over B.base)
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R ℂ)))).obj X ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R ℂ)))).obj Y)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding,
      N ∣ D.denominator ∧ ∃ φ : B.R →+* D.R,
        D.toField.comp φ = (algebraMap B.extension.carrier D.extension.carrier).comp B.toField ∧
        Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X ≅
          (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Y) := by
  obtain ⟨s, ⟨a⟩⟩ := fixed_isomorphism_coefficient_descent B.R ℂ X Y hX hY e
  obtain ⟨D, hdiv, ψ, _, hψ⟩ :=
    B.coefficient_parameter_integral_specialization hAlg s 1 one_ne_zero N hN
  let φ := ψ.comp (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s))
  let b := Spec.map (CommRingCat.ofHom ψ)
  let c := Spec.map (CommRingCat.ofHom φ)
  have hbc : b ≫ CoefficientModels.Coefficients.parameterBaseMap B.R ℂ s = c :=
    (Spec.map_comp (CommRingCat.ofHom (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s)))
      (CommRingCat.ofHom ψ)).symm
  let d (Z : Over B.base) := Group.BaseChangeComparisons.GroupBaseChange.iteratedIso Z (CoefficientModels.Coefficients.parameterBaseMap B.R ℂ s) b c hbc
  exact ⟨D, hdiv, φ, hψ, ⟨(d X).symm ≪≫ (Over.pullback b).mapIso a ≪≫ d Y⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.ArithmeticIsomorphisms
