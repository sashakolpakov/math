import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ProjectiveFormFaithfulness
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseProjectivity

/-! # Albanese Form Faithfulness -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! IntegralModel's actual Betti isomorphism makes pullback of algebraic one-forms
from the literal complex Albanese injective. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic

theorem AlbaneseFormFaithfulness.integralPresentationKaehlerBettiClass (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (ω : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms V.toOver) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.presentationKaehlerBettiClass V.presentation ω = AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass V ω := by
  have h := AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.presentationKaehlerBettiClass_integralPullback V V.presentation (𝟙 V.toOver) ω
  have hid : AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (𝟙 V.toOver) =
      𝟙 (AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) V.toOver 1) := by
    unfold AlgebraicGeometry.Betti.Scheme.schemeBettiMap
    rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map_id, AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id]
  rw [hid, AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_id, LinearMap.id_apply] at h
  exact h.symm

theorem AlbaneseFormFaithfulness.presentationClass_integralTarget_pullback (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (f : P.toOver ⟶ V.toOver) (ω : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms V.toOver) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.presentationKaehlerComplexifiedClass P (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback f ω) =
      (AlgebraicGeometry.PELModuli.IntegralModel.Product.bettiPullbackQ f 1).baseChange ℂ (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerComplexifiedClass V ω) := by
  apply (AlgebraicGeometry.HodgeConjecture.CMExtraction.Mem.bettiComplexification P 1).injective
  change (AlgebraicGeometry.HodgeConjecture.CMExtraction.Mem.bettiComplexification P 1)
    ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Mem.bettiComplexification P 1).symm
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.presentationKaehlerBettiClass P (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback f ω))) = _
  rw [LinearEquiv.apply_symm_apply]
  have h := AlgebraicGeometry.HodgeConjecture.CMExtraction.Naturality.complexification_pullback f 1 (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerComplexifiedClass V ω)
  change _ = AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f
    ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Mem.bettiComplexification V.presentation 1)
      ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Mem.bettiComplexification V.presentation 1).symm (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass V ω))) at h
  rw [LinearEquiv.apply_symm_apply] at h
  have hp := AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.presentationKaehlerBettiClass_pullback P V.presentation f ω
  rw [AlbaneseFormFaithfulness.integralPresentationKaehlerBettiClass] at hp
  exact hp.trans h.symm

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.albanesePullback_injective (hg : D.pel.HasIntegralModelGeometry) :
    Function.Injective (D.pel.albanesePullback hg) := by
  intro ω η h
  let V := (D.pel.actualComplexAlbaneseVariety hg).variety
  let P := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base.singleBaseSpacePresentation D hg
  let f : P.toOver ⟶ V.toOver := (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base.singleBaseSpaceIso D hg).hom ≫ D.pel.complexAlbaneseMap hg
  apply AlgebraicGeometry.AbelianScheme.TateComparison.ProjectiveFormFaithfulness.kaehlerBettiClass_injective V
  apply (AlgebraicGeometry.HodgeConjecture.CMExtraction.Mem.bettiComplexification V.presentation 1).symm.injective
  change AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerComplexifiedClass V ω = AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerComplexifiedClass V η
  apply ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base.nativeAlbaneseBettiEquiv D hg).baseChange ℚ ℂ _ _).injective
  change (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base.nativeAlbaneseBettiEquiv D hg).toLinearMap.baseChange ℂ (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerComplexifiedClass V ω) =
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base.nativeAlbaneseBettiEquiv D hg).toLinearMap.baseChange ℂ (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerComplexifiedClass V η)
  rw [AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base.nativeAlbaneseBettiEquiv_eq_pullback]
  change (AlgebraicGeometry.PELModuli.IntegralModel.Product.bettiPullbackQ f 1).baseChange ℂ (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerComplexifiedClass V ω) =
    (AlgebraicGeometry.PELModuli.IntegralModel.Product.bettiPullbackQ f 1).baseChange ℂ (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerComplexifiedClass V η)
  rw [← AlbaneseFormFaithfulness.presentationClass_integralTarget_pullback P V f,
    ← AlbaneseFormFaithfulness.presentationClass_integralTarget_pullback P V f]
  apply congrArg (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.presentationKaehlerComplexifiedClass P)
  change AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base.singleBaseSpaceIso D hg).hom ≫ D.pel.complexAlbaneseMap hg) ω =
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base.singleBaseSpaceIso D hg).hom ≫ D.pel.complexAlbaneseMap hg) η
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp]
  exact congrArg (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base.singleBaseSpaceIso D hg).hom) h

end

end OAI.RepresentationTheory.Theta.Geometric
