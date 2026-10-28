import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceToCoefficient

/-! # Cover Enlargement -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.CoverEnlargement

noncomputable section

/-! The exact generic comparisons of a relative family and its fixed
arithmetic cover survive every further coefficient enlargement. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace Coefficients
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    {Y : Over (Spec (.of K))} (M : Coefficient.Models.Coefficients.CoefficientModel R K Y)
    {t : Finset K} (hst : M.coefficients ⊆ t)

theorem relative_target_comparison_enlargement
    (X : Over (Spec (.of R))) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (a : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X)
    (a₀ : M.model ⟶ (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)).obj X)
    (ha : M.specialization ≫ a₀.left =
      a.left ≫ (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients X hX).specialization) :
    Coefficient.Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w hst ≫
        ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)).map a₀ ≫ (Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst X).hom).left =
      a.left ≫ (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K t X hX).specialization := by
  let MX := Fixed.CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients X hX
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)
  let e := Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst X
  have hb := Coefficient.BaseChange.Coefficients.genericModelLift_map M.model MX.model M.specialization MX.specialization
    M.cartesian.w MX.cartesian.w a a₀ ha hst
  change _ ≫ ((F.map a₀).left ≫ e.hom.left) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ e.hom.left) hb).trans
      ((Category.assoc a.left _ e.hom.left).trans
        (congrArg (fun k => a.left ≫ k) (Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargement_generic hst X hX))))

theorem relative_cover_comparison_enlargement
    (W : Over (Spec (.of R))) (hW : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism W.hom)
    (q : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj W ⟶ Y)
    (q₀ : (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)).obj W ⟶ M.model)
    (hq : (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients W hW).specialization ≫ q₀.left = q.left ≫ M.specialization) :
    (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K t W hW).specialization ≫
        ((Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst W).inv ≫ (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)).map q₀).left =
      q.left ≫ Coefficient.Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w hst := by
  let MW := Fixed.CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients W hW
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)
  let e := Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst W
  have hb := Coefficient.BaseChange.Coefficients.genericModelLift_map MW.model M.model MW.specialization M.specialization
    MW.cartesian.w M.cartesian.w q q₀ hq hst
  have he := Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargement_generic hst W hW
  calc
    _ = (Coefficient.Morphisms.Coefficients.genericModelLift MW.model MW.specialization MW.cartesian.w hst ≫ e.hom.left) ≫
        (e.inv.left ≫ (F.map q₀).left) :=
      congrArg (fun k => k ≫ (e.inv ≫ F.map q₀).left) he.symm
    _ = Coefficient.Morphisms.Coefficients.genericModelLift MW.model MW.specialization MW.cartesian.w hst ≫ (F.map q₀).left :=
      (Category.assoc _ _ _).trans
        (congrArg (fun k => Coefficient.Morphisms.Coefficients.genericModelLift MW.model MW.specialization MW.cartesian.w hst ≫ k)
          (Over.hom_left_inv_left_assoc e (F.map q₀).left))
    _ = _ := hb

end Coefficients

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.CoverEnlargement
