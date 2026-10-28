import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.CoverCoequalizer
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.CoverEnlargement

/-! # Commutative Family Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CommutativeFamilyCover

noncomputable section

/-! Construct a relative coefficient family whose arithmetic cover map
commutes with the actual base map, retaining the given generic family. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace Coefficients

theorem generic_family_with_cover_has_commutative_model
    {R K : Type} [CommRing R] [IsNoetherianRing R] [Field K] [Algebra R K]
    (X W : Over (Spec (.of R)))
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (hW : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism W.hom)
    (Y : Over (Spec (.of K))) (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (a : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X)
    (q : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj W ⟶ Y)
    (v : W ⟶ X) (hv : q ≫ a = (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map v) :
    ∃ M : Coefficient.Models.Coefficients.CoefficientModel R K Y,
      ∃ (a₀ : M.model ⟶ (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)).obj X)
        (q₀ : (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)).obj W ⟶ M.model),
        M.specialization ≫ a₀.left =
          a.left ≫ (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients X hX).specialization ∧
        (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K M.coefficients W hW).specialization ≫ q₀.left =
          q.left ≫ M.specialization ∧
        q₀ ≫ a₀ = (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K M.coefficients)).map v := by
  obtain ⟨M, a₀, q₀, ha, hq⟩ := GenericFamilyCover.Coefficients.generic_family_with_cover_has_coefficient_model X W hX hW Y hY a q
  obtain ⟨t, hst, hcomm⟩ := Coefficient.CoverCoequalizer.Coefficients.coefficient_cover_commutes_after_enlargement X W hX hW M a q v hv a₀ q₀ ha hq
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)
  let b₀ := F.map a₀ ≫ (Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst X).hom
  let r₀ := (Fixed.SourceEnlargement.Coefficients.fixedSourceEnlargementIso hst W).inv ≫ F.map q₀
  let p := Coefficient.Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w hst
  have hf : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (F.obj M.model).hom := Coefficient.Finiteness.Coefficients.baseChange_finitePresentation _ _ M.finitePresentation
  have hc : IsPullback p Y.hom (F.obj M.model).hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t) :=
    Coefficient.Morphisms.Coefficients.genericModelLift_cartesian M.model M.specialization M.cartesian hst
  let M₁ := Coefficient.Models.Coefficients.CoefficientModel.ofCartesian t (F.obj M.model) hf p hc
  have hM₁ : M₁.specialization = p := Coefficient.Models.Coefficients.CoefficientModel.ofCartesian_specialization _ _ _ _ _
  have hb : p ≫ b₀.left = a.left ≫ (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K t X hX).specialization :=
    Relative.CoverEnlargement.Coefficients.relative_target_comparison_enlargement M hst X hX a a₀ ha
  have hr : (Fixed.CoefficientModels.Coefficients.fixedSourceModel R K t W hW).specialization ≫ r₀.left = q.left ≫ p :=
    Relative.CoverEnlargement.Coefficients.relative_cover_comparison_enlargement M hst W hW q q₀ hq
  have htriangle : r₀ ≫ b₀ = (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R K t)).map v := by
    change (_ ≫ F.map q₀) ≫ (F.map a₀ ≫ _) = _
    rw [Category.assoc, ← Category.assoc (F.map q₀), ← F.map_comp]
    exact hcomm
  exact ⟨M₁, b₀, r₀, (congrArg (fun k => k ≫ b₀.left) hM₁).trans hb,
    hr.trans (congrArg (fun k => q.left ≫ k) hM₁.symm), htriangle⟩

end Coefficients

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CommutativeFamilyCover
