import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.CoefficientSpecialization

/-! # Cartesian Family -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.CartesianFamily

noncomputable section

/-! A given complex family with an actual cartesian arithmetic cover
has an actual cartesian model over a localized ring of integers. The
cover and its parameter schemes remain their literal scalar changes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyCover.Coefficients

theorem arithmetic_cartesian_family_model
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ) [Algebra B.R ℂ]
    (hAlg : algebraMap B.R ℂ = B.embedding.comp B.toField)
    {W T X : Over B.base}
    (hW : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism W.hom) (hT : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism T.hom)
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (a : W ⟶ T) (u : T ⟶ X)
    (Y : Over (Spec (.of ℂ))) (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (q : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R ℂ)))).obj W ⟶ Y)
    (b : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R ℂ)))).obj X)
    (hc : IsPullback ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R ℂ)))).map a) q
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R ℂ)))).map u) b)
    (N₀ : ℕ) (hN₀ : N₀ ≠ 0) :
    ∃ D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding,
      N₀ ∣ D.denominator ∧ ∃ φ : B.R →+* D.R,
        D.toField.comp φ = (algebraMap B.extension.carrier D.extension.carrier).comp B.toField ∧
        let F := Over.pullback (Spec.map (CommRingCat.ofHom φ))
        ∃ (Y₀ : Over D.base) (q₀ : F.obj W ⟶ Y₀) (b₀ : Y₀ ⟶ F.obj X),
          ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y₀.hom ∧ IsPullback (F.map a) q₀ (F.map u) b₀ := by
  obtain ⟨M, b₀, q₀, _, _, hcart⟩ := Cartesian.FamilyCover.Coefficients.generic_cartesian_family_has_coefficient_model hW hT hX a u Y hY q b hc
  obtain ⟨D, hdiv, ψ, _, hbase⟩ := B.coefficient_parameter_integral_specialization hAlg
    M.coefficients 1 one_ne_zero N₀ hN₀
  let φ := ψ.comp (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ M.coefficients))
  let f := Fixed.CoefficientModels.Coefficients.parameterBaseMap B.R ℂ M.coefficients
  let k := Spec.map (CommRingCat.ofHom ψ)
  let c := Spec.map (CommRingCat.ofHom φ)
  have hkc : k ≫ f = c := by
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ M.coefficients)))
      (CommRingCat.ofHom ψ)).symm
  let P := Over.pullback f
  let H := Over.pullback k
  let F := Over.pullback c
  let e := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso f k c hkc
  let Y₀ := H.obj M.model
  let q₁ : F.obj W ⟶ Y₀ := (e.app W).inv ≫ H.map q₀
  let b₁ : Y₀ ⟶ F.obj X := H.map b₀ ≫ (e.app X).hom
  have ha : H.map (P.map a) ≫ (e.app T).hom = (e.app W).hom ≫ F.map a := e.hom.naturality a
  have hu : H.map (P.map u) ≫ (e.app X).hom = (e.app T).hom ≫ F.map u := e.hom.naturality u
  have hs : IsPullback (F.map a) q₁ (F.map u) b₁ := by
    exact (hcart.map H).of_iso (e.app W) (e.app T) (Iso.refl Y₀) (e.app X) ha
      (by
        change H.map q₀ ≫ 𝟙 _ = (e.app W).hom ≫ ((e.app W).inv ≫ H.map q₀)
        rw [Category.comp_id, Iso.hom_inv_id_assoc]) hu
      (by
        change H.map b₀ ≫ (e.app X).hom = 𝟙 _ ≫ (H.map b₀ ≫ (e.app X).hom)
        exact (Category.id_comp _).symm)
  exact ⟨D, hdiv, φ, hbase, Y₀, q₁, b₁, Coefficient.Finiteness.Coefficients.baseChange_finitePresentation k M.model M.finitePresentation, hs⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.CartesianFamily
