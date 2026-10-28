import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CommutativeFamilyCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.GenericCartesianComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GenericCartesian
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverPullbackFinitePresentation

/-! # Family Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyCover

noncomputable section

/-! Construct an actual cartesian family-cover diagram over a finite
coefficient ring from the given generic family and fixed arithmetic cover. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace Coefficients

theorem generic_cartesian_family_has_coefficient_model
    {R K : Type} [CommRing R] [IsNoetherianRing R] [Field K] [Algebra R K]
    {W T X : Over (Spec (.of R))}
    (hW : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism W.hom) (hT : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism T.hom)
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (a : W ⟶ T) (u : T ⟶ X)
    (Y : Over (Spec (.of K))) (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (q : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj W ⟶ Y)
    (b : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X)
    (hc : IsPullback ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map a) q
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map u) b) :
    ∃ M : Coefficient.Models.Coefficients.CoefficientModel R K Y,
      ∃ (b₀ : M.model ⟶ (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)).obj X)
        (q₀ : (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)).obj W ⟶ M.model),
        M.specialization ≫ b₀.left = b.left ≫ (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients X hX).specialization ∧
        (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients W hW).specialization ≫ q₀.left = q.left ≫ M.specialization ∧
        IsPullback ((Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)).map a) q₀
          ((Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)).map u) b₀ := by
  let G := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  have hv : q ≫ b = G.map (a ≫ u) := hc.w.symm.trans (G.map_comp a u).symm
  obtain ⟨M, b₀, q₀, hb, hq, hcomm⟩ :=
    CommutativeFamilyCover.Coefficients.generic_family_with_cover_has_commutative_model X W hX hW Y hY b q (a ≫ u) hv
  let s := M.coefficients
  let P := Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s)
  have hw : P.map a ≫ P.map u = q₀ ≫ b₀ := (P.map_comp a u).symm.trans hcomm.symm
  have hWP : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (P.obj W).hom := Coefficient.Finiteness.Coefficients.baseChange_finitePresentation _ _ hW
  have hTP : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (P.obj T).hom := Coefficient.Finiteness.Coefficients.baseChange_finitePresentation _ _ hT
  have hXP : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (P.obj X).hom := Coefficient.Finiteness.Coefficients.baseChange_finitePresentation _ _ hX
  have hPB := OverPullbackFinitePresentation.coefficient_pullback_finitePresentation (P.map u) b₀ hTP M.finitePresentation hXP
  have hgeneric := Relative.GenericCartesianComparison.Coefficients.relative_generic_cartesian_comparison hW hT hX a u M q b hc q₀ b₀ hq hb
  obtain ⟨t, hst, hcart⟩ := Coefficient.GenericCartesian.Coefficients.coefficient_generic_cartesian_after_enlargement
    (P.map a) q₀ (P.map u) b₀ hw hWP hPB hgeneric
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)
  let P' := Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t)
  let eW := Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst W
  let eT := Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst T
  let eX := Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst X
  let e := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K s) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)
    (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t) (Fixed.CoefficientModels.Coefficients.coefficient_parameterBaseMap R K hst)
  let b₁ := F.map b₀ ≫ eX.hom
  let q₁ := eW.inv ≫ F.map q₀
  have ha : F.map (P.map a) ≫ eT.hom = eW.hom ≫ P'.map a := e.hom.naturality a
  have hu : F.map (P.map u) ≫ eX.hom = eT.hom ≫ P'.map u := e.hom.naturality u
  have hcart₁ : IsPullback (P'.map a) q₁ (P'.map u) b₁ := by
    exact hcart.of_iso eW eT (Iso.refl (F.obj M.model)) eX ha
      (by
        change F.map q₀ ≫ 𝟙 _ = eW.hom ≫ (eW.inv ≫ F.map q₀)
        rw [Category.comp_id, Iso.hom_inv_id_assoc]) hu
      (by
        change F.map b₀ ≫ eX.hom = 𝟙 _ ≫ (F.map b₀ ≫ eX.hom)
        exact (Category.id_comp _).symm)
  let p := Coefficient.Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w hst
  have hf : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (F.obj M.model).hom := Coefficient.Finiteness.Coefficients.baseChange_finitePresentation _ _ M.finitePresentation
  have hp : IsPullback p Y.hom (F.obj M.model).hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t) :=
    Coefficient.Morphisms.Coefficients.genericModelLift_cartesian M.model M.specialization M.cartesian hst
  let M₁ := Coefficient.Models.Coefficients.CoefficientModel.ofCartesian t (F.obj M.model) hf p hp
  have hM₁ : M₁.specialization = p := Coefficient.Models.Coefficients.CoefficientModel.ofCartesian_specialization _ _ _ _ _
  have hb₁ : p ≫ b₁.left = b.left ≫ (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K t X hX).specialization :=
    Relative.CoverEnlargement.Coefficients.relative_target_comparison_enlargement M hst X hX b b₀ hb
  have hq₁ : (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K t W hW).specialization ≫ q₁.left = q.left ≫ p :=
    Relative.CoverEnlargement.Coefficients.relative_cover_comparison_enlargement M hst W hW q q₀ hq
  exact ⟨M₁, b₁, q₁, (congrArg (fun k => k ≫ b₁.left) hM₁).trans hb₁,
    hq₁.trans (congrArg (fun k => q.left ≫ k) hM₁.symm), hcart₁⟩

end Coefficients

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyCover
