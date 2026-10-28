import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverIsoNaturality
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceMorphismSpecialization

/-! # Generic Cartesian Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.GenericCartesianComparison.Coefficients

noncomputable section

/-! The given generic cartesian family comparison is the literal
generic pullback of any model with the exact specialization equations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem relative_generic_cartesian_comparison
    {R K : Type} [CommRing R] [Field K] [Algebra R K]
    {W T X : Over (Spec (.of R))}
    (hW : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism W.hom) (hT : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism T.hom)
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (a : W ⟶ T) (u : T ⟶ X)
    {Y : Over (Spec (.of K))} (M : Coefficient.Models.Coefficients.CoefficientModel R K Y)
    (q : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj W ⟶ Y)
    (b : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X)
    (hc : IsPullback ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map a) q
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map u) b)
    (q₀ : (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)).obj W ⟶ M.model)
    (b₀ : M.model ⟶ (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)).obj X)
    (hq : (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients W hW).specialization ≫ q₀.left = q.left ≫ M.specialization)
    (hb : M.specialization ≫ b₀.left = b.left ≫ (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients X hX).specialization) :
    let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K M.coefficients)
    let P := Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)
    IsPullback (F.map (P.map a)) (F.map q₀) (F.map (P.map u)) (F.map b₀) := by
  let s := M.coefficients
  let G := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  let P := Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)
  let MW := Fixed.CoefficientModels.Coefficients.fixedSourceModel R K s W hW
  let MT := Fixed.CoefficientModels.Coefficients.fixedSourceModel R K s T hT
  let MX := Fixed.CoefficientModels.Coefficients.fixedSourceModel R K s X hX
  have ha := OverIsoNaturality.over_model_iso_naturality (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s) MW.genericIso MT.genericIso
    (G.map a) (P.map a) (Fixed.SourceMorphismSpecialization.Coefficients.fixedSourceModel_specialization_map s W T hW hT a)
  have hu := OverIsoNaturality.over_model_iso_naturality (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s) MT.genericIso MX.genericIso
    (G.map u) (P.map u) (Fixed.SourceMorphismSpecialization.Coefficients.fixedSourceModel_specialization_map s T X hT hX u)
  have hq' := OverIsoNaturality.over_model_iso_naturality (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s) MW.genericIso M.genericIso q q₀ hq
  have hb' := OverIsoNaturality.over_model_iso_naturality (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s) M.genericIso MX.genericIso b b₀ hb
  exact hc.of_iso' MW.genericIso MT.genericIso M.genericIso MX.genericIso ha.symm hq'.symm hu.symm hb'.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.GenericCartesianComparison.Coefficients
