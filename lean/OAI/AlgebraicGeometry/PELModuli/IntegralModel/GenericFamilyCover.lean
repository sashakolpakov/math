import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.Coefficient
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceToCoefficient

/-! # Generic Family Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericFamilyCover.Coefficients

noncomputable section

/-! Construct a generic-family model and its actual arithmetic cover
map over one finite coefficient ring, with both comparisons exact. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem generic_family_with_cover_has_coefficient_model
    {R K : Type} [CommRing R] [IsNoetherianRing R] [Field K] [Algebra R K]
    (X W : Over (Spec (.of R)))
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (hW : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism W.hom)
    (Y : Over (Spec (.of K))) (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (a : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X)
    (q : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj W ⟶ Y) :
    ∃ M : Coefficient.Models.Coefficients.CoefficientModel R K Y,
      ∃ (a₀ : M.model ⟶ (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)).obj X)
        (q₀ : (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)).obj W ⟶ M.model),
        M.specialization ≫ a₀.left =
          a.left ≫ (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients X hX).specialization ∧
        (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients W hW).specialization ≫ q₀.left =
          q.left ≫ M.specialization := by
  obtain ⟨s, Y₀, a₀, p, hfp, hcart, ha⟩ := Relative.Coefficient.Coefficients.family_has_relative_coefficient_model X hX Y hY a
  let M := Coefficient.Models.Coefficients.CoefficientModel.ofCartesian s Y₀ hfp p hcart
  have hM : M.specialization = p := Coefficient.Models.Coefficients.CoefficientModel.ofCartesian_specialization _ _ _ _ _
  have haM : M.specialization ≫ a₀.left =
      a.left ≫ (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients X hX).specialization :=
    (congrArg (fun k => k ≫ a₀.left) hM).trans ha
  obtain ⟨t, hst, q₀, b₀, hq, hb⟩ := Fixed.SourceToCoefficient.Coefficients.relative_coefficient_model_with_cover_maps X W hX hW M a a₀ haM q
  let Y₁ := (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)).obj M.model
  let p₁ := Coefficient.Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w hst
  have hf₁ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y₁.hom := Coefficient.Finiteness.Coefficients.baseChange_finitePresentation _ _ M.finitePresentation
  have hc₁ : IsPullback p₁ Y.hom Y₁.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t) :=
    Coefficient.Morphisms.Coefficients.genericModelLift_cartesian M.model M.specialization M.cartesian hst
  let M₁ := Coefficient.Models.Coefficients.CoefficientModel.ofCartesian t Y₁ hf₁ p₁ hc₁
  have hM₁ : M₁.specialization = p₁ := Coefficient.Models.Coefficients.CoefficientModel.ofCartesian_specialization _ _ _ _ _
  exact ⟨M₁, b₀, q₀, (congrArg (fun k => k ≫ b₀.left) hM₁).trans hb,
    hq.trans (congrArg (fun k => q.left ≫ k) hM₁.symm)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericFamilyCover.Coefficients
