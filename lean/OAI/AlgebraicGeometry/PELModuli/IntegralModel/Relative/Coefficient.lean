import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GeneralModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Morphisms
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceEnlargement
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Finiteness

/-! # Coefficient -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.Coefficient.Coefficients

noncomputable section

/-! Construct a coefficient model for an actual generic family while
keeping its original arithmetic base as the literal scalar-changed base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem family_has_relative_coefficient_model
    {R K : Type} [CommRing R] [IsNoetherianRing R] [Field K] [Algebra R K]
    (X : Over (Spec (.of R))) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (Y : Over (Spec (.of K))) (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (a : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X) :
    ∃ (s : Finset K) (Y₀ : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s))
      (a₀ : Y₀ ⟶ (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X)
      (p : Y.left ⟶ Y₀.left),
      ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y₀.hom ∧
      IsPullback p Y.hom Y₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s) ∧
      p ≫ a₀.left = a.left ≫ (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K s X hX).specialization := by
  obtain ⟨M⟩ := Coefficient.GeneralModels.Coefficients.scheme_has_coefficient_model (R₀ := R) Y hY
  let MX := Fixed.CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients X hX
  obtain ⟨t, hst, b, hb⟩ := Coefficient.Morphisms.Coefficients.morphism_between_models_descends M.model MX.model
    M.finitePresentation MX.finitePresentation M.specialization MX.specialization
    M.cartesian MX.cartesian a
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)
  let e := Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst X
  let a₀ := b ≫ e.hom
  let p := Coefficient.Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w hst
  refine ⟨t, F.obj M.model, a₀, p, Coefficient.Finiteness.Coefficients.baseChange_finitePresentation _ _ M.finitePresentation,
    Coefficient.Morphisms.Coefficients.genericModelLift_cartesian M.model M.specialization M.cartesian hst, ?_⟩
  change p ≫ (b.left ≫ e.hom.left) = _
  exact (Category.assoc p b.left e.hom.left).symm.trans
    ((congrArg (fun k => k ≫ e.hom.left) hb).trans
      ((Category.assoc a.left _ e.hom.left).trans
        (congrArg (fun k => a.left ≫ k) (Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargement_generic hst X hX))))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.Coefficient.Coefficients
