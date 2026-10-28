import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ClosedForms
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerNaturality
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveNaturality
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectivePurePullback

/-! # Kaehler Classes -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic

noncomputable section

section

/-! Naturality of the integration-defined Betti class of the actual Kähler realization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped ContDiff

def closedKaehlerRealization (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    AbelianScheme.TateComparison.FormConstants.OneForms V.toOver →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1 := by
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  let : V.toOver.left.IsSeparated := Intrinsic.IntrinsicForms.integralProjective_separated V
  exact (KaehlerGluing.globalSmoothForm V.toOver).codRestrict _ (Intrinsic.ClosedForms.projectiveKaehlerForm_closed V)

def kaehlerBettiClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    AbelianScheme.TateComparison.FormConstants.OneForms V.toOver →ₗ[ℂ] V.complexCohomology 1 where
  toFun form := (V.deRhamBettiIso 1).hom (V.deRhamClass 1 (closedKaehlerRealization V form))
  map_add' form other := by simp only [map_add]
  map_smul' c form := by simp only [map_smul, RingHom.id_apply]

theorem closedKaehlerRealization_pullback {V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : V.toOver ⟶ W.toOver) (form : AbelianScheme.TateComparison.FormConstants.OneForms W.toOver) :
    closedKaehlerRealization V (AbelianScheme.TateComparison.FormConstants.formsPullback f form) =
      Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
        (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map f ∞) 1 (closedKaehlerRealization W form) := by
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  let : V.toOver.left.IsSeparated := Intrinsic.IntrinsicForms.integralProjective_separated V
  let : IsIntegral W.toOver.left := W.property
  let : Smooth W.toOver.hom := W.presentation.smooth
  let : W.toOver.left.IsSeparated := Intrinsic.IntrinsicForms.integralProjective_separated W
  apply Subtype.ext
  exact KaehlerNaturality.globalSmoothForm_pullback f form

/-- Pullback of algebraic forms commutes with their actual singular Betti class. -/
theorem kaehlerBettiClass_pullback {V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : V.toOver ⟶ W.toOver) (form : AbelianScheme.TateComparison.FormConstants.OneForms W.toOver) :
    kaehlerBettiClass V (AbelianScheme.TateComparison.FormConstants.formsPullback f form) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f (kaehlerBettiClass W form) := by
  have h := ConcreteCategory.congr_hom (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_naturality f 1)
    (W.deRhamClass 1 (closedKaehlerRealization W form))
  have hc := Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback_closedFormClass f 1 (closedKaehlerRealization W form)
  change _ = (V.deRhamBettiIso 1).hom
    (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback f 1
      (W.deRhamClass 1 (closedKaehlerRealization W form))) at h
  rw [hc, ← closedKaehlerRealization_pullback f form] at h
  exact h.symm

def kaehlerComplexifiedClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    AbelianScheme.TateComparison.FormConstants.OneForms V.toOver →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification (V.rationalCohomology 1) :=
  (Mem.bettiComplexification V.presentation 1).symm.toLinearMap.comp (kaehlerBettiClass V)

theorem kaehlerComplexifiedClass_pullback {V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : V.toOver ⟶ W.toOver) (form : AbelianScheme.TateComparison.FormConstants.OneForms W.toOver) :
    kaehlerComplexifiedClass V (AbelianScheme.TateComparison.FormConstants.formsPullback f form) =
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 f).hom.baseChange ℂ (kaehlerComplexifiedClass W form) := by
  apply (Mem.bettiComplexification V.presentation 1).injective
  change (Mem.bettiComplexification V.presentation 1)
    ((Mem.bettiComplexification V.presentation 1).symm
      (kaehlerBettiClass V (AbelianScheme.TateComparison.FormConstants.formsPullback f form))) = _
  rw [LinearEquiv.apply_symm_apply]
  have h := Naturality.complexification_pullback f 1 (kaehlerComplexifiedClass W form)
  change _ = Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f
    ((Mem.bettiComplexification W.presentation 1)
      ((Mem.bettiComplexification W.presentation 1).symm (kaehlerBettiClass W form))) at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact (kaehlerBettiClass_pullback f form).trans h.symm

end

/-! Integration-defined Kähler classes on arbitrary smooth projective
presentations, assembled from their genuine clopen integral components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem kaehlerBettiClass_pure (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (form : AbelianScheme.TateComparison.FormConstants.OneForms V.toOver) :
    kaehlerBettiClass V form ∈ V.pureBettiSubspace 1 0 := by
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  let : V.toOver.left.IsSeparated := Intrinsic.IntrinsicForms.integralProjective_separated V
  exact (V.mem_pureBettiSubspace_iff 1 0 _).mpr
    ⟨closedKaehlerRealization V form,
      (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mp
        (OpenPurity.Kaehler.globalSmoothForm_pure V.toOver form), rfl⟩

def presentationKaehlerBettiClass (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    AbelianScheme.TateComparison.FormConstants.OneForms P.toOver →ₗ[ℂ] P.complexCohomology 1 :=
  (P.componentBettiEquiv (ModuleCat.of ℂ ℂ) 1).symm.toLinearMap.comp
    (LinearMap.pi (fun C => (kaehlerBettiClass (P.componentVariety C)).comp
      (AbelianScheme.TateComparison.FormConstants.formsPullback (P.componentInclusionOver C))))

theorem presentationKaehlerBettiClass_component (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (form : AbelianScheme.TateComparison.FormConstants.OneForms P.toOver) (C : irreducibleComponents P.carrier) :
    P.componentBettiEquiv (ModuleCat.of ℂ ℂ) 1 (presentationKaehlerBettiClass P form) C =
      kaehlerBettiClass (P.componentVariety C) (AbelianScheme.TateComparison.FormConstants.formsPullback (P.componentInclusionOver C) form) := by
  exact congrFun ((P.componentBettiEquiv (ModuleCat.of ℂ ℂ) 1).apply_symm_apply _) C

theorem presentationKaehlerBettiClass_pure (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (form : AbelianScheme.TateComparison.FormConstants.OneForms P.toOver) :
    presentationKaehlerBettiClass P form ∈ P.pureBettiSubspace 1 0 := by
  apply (P.mem_pureBettiSubspace_iff 1 0 _).mpr
  intro C
  rw [presentationKaehlerBettiClass_component]
  exact kaehlerBettiClass_pure _ _

theorem presentationKaehlerBettiClass_integralPullback (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (f : V.toOver ⟶ P.toOver) (form : AbelianScheme.TateComparison.FormConstants.OneForms P.toOver) :
    kaehlerBettiClass V (AbelianScheme.TateComparison.FormConstants.formsPullback f form) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f (presentationKaehlerBettiClass P form) := by
  obtain ⟨C, g, hfac⟩ := AlgebraicTopology.Kunneth.PresentationPullbackPurity.Constructions.integralMorphism_factors_component V P f
  have hclass := kaehlerBettiClass_pullback g (AbelianScheme.TateComparison.FormConstants.formsPullback (P.componentInclusionOver C) form)
  have hinc := presentationKaehlerBettiClass_component P form C
  rw [P.componentBettiEquiv_apply] at hinc
  rw [← hfac, AbelianScheme.TateComparison.FormConstants.formsPullback_comp, AlgebraicTopology.Kunneth.PresentationPullbackPurity.Constructions.schemeBettiMap_comp_apply]
  exact hclass.trans (congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 g) hinc.symm)

theorem presentationKaehlerBettiClass_pullback (P Q : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (f : P.toOver ⟶ Q.toOver) (form : AbelianScheme.TateComparison.FormConstants.OneForms Q.toOver) :
    presentationKaehlerBettiClass P (AbelianScheme.TateComparison.FormConstants.formsPullback f form) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f (presentationKaehlerBettiClass Q form) := by
  apply (P.componentBettiEquiv (ModuleCat.of ℂ ℂ) 1).injective
  funext C
  rw [presentationKaehlerBettiClass_component, P.componentBettiEquiv_apply,
    ← AlgebraicTopology.Kunneth.PresentationPullbackPurity.Constructions.schemeBettiMap_comp_apply]
  have h := presentationKaehlerBettiClass_integralPullback (P.componentVariety C) Q
    (P.componentInclusionOver C ≫ f) form
  rw [AbelianScheme.TateComparison.FormConstants.formsPullback_comp] at h
  exact h

def presentationKaehlerComplexifiedClass (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    AbelianScheme.TateComparison.FormConstants.OneForms P.toOver →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification (P.rationalCohomology 1) :=
  (Mem.bettiComplexification P 1).symm.toLinearMap.comp (presentationKaehlerBettiClass P)

theorem presentationKaehlerComplexifiedClass_holomorphic
    (hHodgeDecomposition : Mem.HodgeDecompositionInput) (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (form : AbelianScheme.TateComparison.FormConstants.OneForms P.toOver) :
    presentationKaehlerComplexifiedClass P form ∈ (Mem.canonicalH1 hHodgeDecomposition P).holomorphic := by
  change (Mem.bettiComplexification P 1)
    ((Mem.bettiComplexification P 1).symm (presentationKaehlerBettiClass P form)) ∈
      P.pureBettiSubspace 1 0
  rw [LinearEquiv.apply_symm_apply]
  exact presentationKaehlerBettiClass_pure P form

theorem presentationKaehlerComplexifiedClass_integralPullback (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (f : V.toOver ⟶ P.toOver) (form : AbelianScheme.TateComparison.FormConstants.OneForms P.toOver) :
    kaehlerComplexifiedClass V (AbelianScheme.TateComparison.FormConstants.formsPullback f form) =
      (PELModuli.IntegralModel.Product.bettiPullbackQ f 1).baseChange ℂ (presentationKaehlerComplexifiedClass P form) := by
  apply (Mem.bettiComplexification V.presentation 1).injective
  change (Mem.bettiComplexification V.presentation 1)
    ((Mem.bettiComplexification V.presentation 1).symm
      (kaehlerBettiClass V (AbelianScheme.TateComparison.FormConstants.formsPullback f form))) = _
  rw [LinearEquiv.apply_symm_apply]
  have h := Naturality.complexification_pullback f 1 (presentationKaehlerComplexifiedClass P form)
  change _ = Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f
    ((Mem.bettiComplexification P 1)
      ((Mem.bettiComplexification P 1).symm (presentationKaehlerBettiClass P form))) at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact (presentationKaehlerBettiClass_integralPullback V P f form).trans h.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic
