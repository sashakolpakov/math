import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceEnlargement
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Finiteness

/-! # Source To Coefficient -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceToCoefficient.Coefficients

noncomputable section

section

/-! Extend an actual generic morphism from an existing arithmetic
scheme to a constructed coefficient model, keeping the source literal. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem morphism_from_fixed_source_to_coefficient_model
    {R K : Type} [CommRing R] [Field K] [Algebra R K]
    (X : Over (Spec (.of R))) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    {Y : Over (Spec (.of K))} (M : Coefficient.Models.Coefficients.CoefficientModel R K Y)
    (a : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X ⟶ Y) :
    ∃ (t : Finset K) (hst : M.coefficients ⊆ t)
      (a₀ : (Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K t)).obj X ⟶
        (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)).obj M.model),
      (CoefficientModels.Coefficients.fixedSourceModel R K t X hX).specialization ≫ a₀.left =
        a.left ≫ Coefficient.Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w hst := by
  let MX := CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients X hX
  obtain ⟨t, hst, b, hb⟩ := Coefficient.Morphisms.Coefficients.morphism_between_models_descends MX.model M.model
    MX.finitePresentation M.finitePresentation MX.specialization M.specialization
    MX.cartesian M.cartesian a
  let e := SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst X
  let a₀ := e.inv ≫ b
  have he := SourceEnlargement.Coefficients.fixedSourceEnlargement_generic hst X hX
  refine ⟨t, hst, a₀, ?_⟩
  calc
    _ = (Coefficient.Morphisms.Coefficients.genericModelLift MX.model MX.specialization MX.cartesian.w hst ≫ e.hom.left) ≫
        (e.inv.left ≫ b.left) := congrArg (fun k => k ≫ a₀.left) he.symm
    _ = Coefficient.Morphisms.Coefficients.genericModelLift MX.model MX.specialization MX.cartesian.w hst ≫ b.left := by
      exact (Category.assoc _ _ _).trans
        (congrArg (fun k => Coefficient.Morphisms.Coefficients.genericModelLift MX.model MX.specialization MX.cartesian.w hst ≫ k)
          (Over.hom_left_inv_left_assoc e b.left))
    _ = _ := hb

end

/-! Extend the actual arithmetic cover map to a relative coefficient
family and retain both exact generic comparison equations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem relative_coefficient_model_with_cover_maps
    {R K : Type} [CommRing R] [Field K] [Algebra R K]
    (X W : Over (Spec (.of R)))
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (hW : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism W.hom)
    {Y : Over (Spec (.of K))} (M : Coefficient.Models.Coefficients.CoefficientModel R K Y)
    (a : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X)
    (a₀ : M.model ⟶ (Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)).obj X)
    (ha : M.specialization ≫ a₀.left =
      a.left ≫ (CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients X hX).specialization)
    (q : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj W ⟶ Y) :
    ∃ (t : Finset K) (hst : M.coefficients ⊆ t)
      (q₀ : (Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K t)).obj W ⟶
        (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)).obj M.model)
      (b₀ : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)).obj M.model ⟶
        (Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K t)).obj X),
      (CoefficientModels.Coefficients.fixedSourceModel R K t W hW).specialization ≫ q₀.left =
        q.left ≫ Coefficient.Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w hst ∧
      Coefficient.Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w hst ≫ b₀.left =
        a.left ≫ (CoefficientModels.Coefficients.fixedSourceModel R K t X hX).specialization := by
  obtain ⟨t, hst, q₀, hq⟩ := morphism_from_fixed_source_to_coefficient_model W hW M q
  let MX := CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients X hX
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)
  let e := SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst X
  let b₀ := F.map a₀ ≫ e.hom
  have hb := Coefficient.BaseChange.Coefficients.genericModelLift_map M.model MX.model M.specialization MX.specialization
    M.cartesian.w MX.cartesian.w a a₀ ha hst
  refine ⟨t, hst, q₀, b₀, hq, ?_⟩
  change Coefficient.Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w hst ≫
    ((F.map a₀).left ≫ e.hom.left) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ e.hom.left) hb).trans
      ((Category.assoc a.left _ e.hom.left).trans
        (congrArg (fun k => a.left ≫ k) (SourceEnlargement.Coefficients.fixedSourceEnlargement_generic hst X hX))))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceToCoefficient.Coefficients
