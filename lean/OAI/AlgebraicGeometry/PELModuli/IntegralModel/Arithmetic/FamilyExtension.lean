import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.TowerDenominatorMap
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyFunctorTransport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.CartesianFamily

/-! # Family Extension -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.FamilyExtension

noncomputable section

/-! Extend an actual fixed-field family model to a further arithmetic
base, retaining its literal covering diagram and relation equations.
The map of localized integer rings is constructed from divisibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem arithmetic_family_model_extend
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ)
    (D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding)
    (n : ℕ) (hn : n ≠ 0) (hdiv : n ∣ D.denominator)
    (φ₀ : B.R →+* (B.withDenominator n hn).R)
    (hφ₀ : (B.withDenominator n hn).toField.comp φ₀ = B.toField)
    (φ : B.R →+* D.R)
    (hφ : D.toField.comp φ = (algebraMap B.extension.carrier D.extension.carrier).comp B.toField)
    {W T X Z : Over B.base} (a : W ⟶ T) (u : T ⟶ X) (s t : Z ⟶ W)
    (Y₀ : Over (B.withDenominator n hn).base)
    (q₀ : (Over.pullback (Spec.map (CommRingCat.ofHom φ₀))).obj W ⟶ Y₀)
    (b₀ : Y₀ ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ₀))).obj X)
    (hY₀ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y₀.hom)
    (hc : IsPullback ((Over.pullback (Spec.map (CommRingCat.ofHom φ₀))).map a) q₀
      ((Over.pullback (Spec.map (CommRingCat.ofHom φ₀))).map u) b₀)
    (he : (Over.pullback (Spec.map (CommRingCat.ofHom φ₀))).map s ≫ q₀ =
      (Over.pullback (Spec.map (CommRingCat.ofHom φ₀))).map t ≫ q₀) :
    let F := Over.pullback (Spec.map (CommRingCat.ofHom φ))
    ∃ (Y : Over D.base) (q : F.obj W ⟶ Y) (b : Y ⟶ F.obj X),
      ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom ∧ IsPullback (F.map a) q (F.map u) b ∧
        F.map s ≫ q = F.map t ≫ q := by
  obtain ⟨ψ, hψ⟩ := B.exists_tower_denominator_map D n hn hdiv
  have hψφ := B.tower_denominator_map_compatible D n hn ψ hψ φ₀ hφ₀ φ hφ
  let c₀ := Spec.map (CommRingCat.ofHom φ₀)
  let c := Spec.map (CommRingCat.ofHom φ)
  let k := Spec.map (CommRingCat.ofHom ψ)
  have hkc : k ≫ c₀ = c := by
    change Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ₀) =
      Spec.map (CommRingCat.ofHom φ)
    rw [← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hψφ
  let F₀ := Over.pullback c₀
  let G := Over.pullback k
  let F := Over.pullback c
  let e := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso c₀ k c hkc
  exact ⟨G.obj Y₀, (e.app W).inv ≫ G.map q₀, G.map b₀ ≫ (e.app X).hom,
    Coefficient.Finiteness.Coefficients.baseChange_finitePresentation k Y₀ hY₀,
    Cartesian.FamilyFunctorTransport.cartesian_family_functor_transport F₀ G F e a u q₀ b₀ hc,
    Cartesian.FamilyFunctorTransport.coequalizer_functor_transport F₀ G F e s t q₀ he⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.FamilyExtension
