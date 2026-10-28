import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses

/-! # Theta Class -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass

noncomputable section

/-! The actual theta class in native Albanese H¹, defined by integration on
the projective source and the original IntegralModel Betti isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def nativeKaehlerClass (hg : D.pel.HasIntegralModelGeometry) :
    D.pel.OneFormsA →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1 :=
  ((Base.nativeAlbaneseBettiEquiv D hg).symm.toLinearMap.baseChange ℂ).comp
    ((KaehlerClasses.Intrinsic.presentationKaehlerComplexifiedClass (Base.singleBaseSpacePresentation D hg)).comp
      (AbelianScheme.TateComparison.FormConstants.formsPullback ((Base.singleBaseSpaceIso D hg).hom ≫ D.pel.complexAlbaneseMap hg)))

theorem nativeKaehlerClass_albanese (hg : D.pel.HasIntegralModelGeometry) (form : D.pel.OneFormsA) :
    (Base.nativeAlbaneseBettiEquiv D hg).toLinearMap.baseChange ℂ (nativeKaehlerClass D hg form) =
      KaehlerClasses.Intrinsic.presentationKaehlerComplexifiedClass (Base.singleBaseSpacePresentation D hg)
        (AbelianScheme.TateComparison.FormConstants.formsPullback ((Base.singleBaseSpaceIso D hg).hom ≫ D.pel.complexAlbaneseMap hg) form) := by
  exact ((Base.nativeAlbaneseBettiEquiv D hg).baseChange ℚ ℂ _ _).apply_symm_apply _

theorem nativeKaehlerClass_holomorphic (hHodgeDecomposition : Mem.HodgeDecompositionInput)
    (hg : D.pel.HasIntegralModelGeometry) (form : D.pel.OneFormsA) :
    nativeKaehlerClass D hg form ∈ (Base.nativeH1 D hHodgeDecomposition hg).holomorphic := by
  exact ((Mem.canonicalH1 hHodgeDecomposition (Base.singleBaseSpacePresentation D hg)).transport_isHodgeMap
    (Base.nativeAlbaneseBettiEquiv D hg).symm) _
      (KaehlerClasses.Intrinsic.presentationKaehlerComplexifiedClass_holomorphic hHodgeDecomposition (Base.singleBaseSpacePresentation D hg) _)

theorem nativeKaehlerClass_component (hg : D.pel.HasIntegralModelGeometry)
    (j : Fin D.pel.componentCount) (form : D.pel.OneFormsA) :
    (Forms.componentRestriction D hg j).baseChange ℂ (nativeKaehlerClass D hg form) =
      KaehlerClasses.Intrinsic.kaehlerComplexifiedClass (D.componentVariety hg j)
        (AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion j) (D.pel.albanesePullback hg form)) := by
  let P := Base.singleBaseSpacePresentation D hg
  let a := (Base.singleBaseSpaceIso D hg).hom ≫ D.pel.complexAlbaneseMap hg
  let f : (D.componentVariety hg j).toOver ⟶ P.toOver :=
    D.componentComplexInclusion j ≫ (Base.singleBaseSpaceIso D hg).inv
  have hfac : f ≫ a = D.componentComplexInclusion j ≫ D.pel.complexAlbaneseMap hg := by
    exact (Category.assoc _ _ _).trans
      (congrArg (fun g => D.componentComplexInclusion j ≫ g)
        ((Base.singleBaseSpaceIso D hg).inv_hom_id_assoc (D.pel.complexAlbaneseMap hg)))
  have hr : Forms.componentRestriction D hg j =
      (PELModuli.IntegralModel.Product.bettiPullbackQ f 1).comp (Base.nativeAlbaneseBettiEquiv D hg).toLinearMap := by
    rw [Base.nativeAlbaneseBettiEquiv_eq_pullback, ← PELModuli.IntegralModel.Product.bettiPullbackQ_comp]
    exact congrArg (fun g => PELModuli.IntegralModel.Product.bettiPullbackQ g 1) hfac.symm
  have hstart : (Forms.componentRestriction D hg j).baseChange ℂ (nativeKaehlerClass D hg form) =
      (PELModuli.IntegralModel.Product.bettiPullbackQ f 1).baseChange ℂ
        ((Base.nativeAlbaneseBettiEquiv D hg).toLinearMap.baseChange ℂ (nativeKaehlerClass D hg form)) := by
    exact (congrArg (fun L : D.pel.H1 →ₗ[ℚ] (D.componentVariety hg j).rationalCohomology 1 =>
      L.baseChange ℂ (nativeKaehlerClass D hg form)) hr).trans
      (LinearMap.congr_fun (LinearMap.baseChange_comp
        (Base.nativeAlbaneseBettiEquiv D hg).toLinearMap (PELModuli.IntegralModel.Product.bettiPullbackQ f 1)) _)
  refine hstart.trans ?_
  rw [nativeKaehlerClass_albanese]
  have h := KaehlerClasses.Intrinsic.presentationKaehlerComplexifiedClass_integralPullback (D.componentVariety hg j)
    P f (AbelianScheme.TateComparison.FormConstants.formsPullback a form)
  have hforms : AbelianScheme.TateComparison.FormConstants.formsPullback f (AbelianScheme.TateComparison.FormConstants.formsPullback a form) =
      AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion j) (D.pel.albanesePullback hg form) := by
    have hcomp := congrArg (fun L => L form) (AbelianScheme.TateComparison.FormConstants.formsPullback_comp f a)
    rw [hfac, AbelianScheme.TateComparison.FormConstants.formsPullback_comp] at hcomp
    exact hcomp.symm
  rw [hforms] at h
  exact h.symm

def nativeThetaClass (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) :
    D.sphericalInputs →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1 :=
  (nativeKaehlerClass D hg).comp Θ

theorem nativeThetaClass_holomorphic (hHodgeDecomposition : Mem.HodgeDecompositionInput)
    (hg : D.pel.HasIntegralModelGeometry) (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (φ : D.sphericalInputs) :
    nativeThetaClass D hg Θ φ ∈ (Base.nativeH1 D hHodgeDecomposition hg).holomorphic :=
  nativeKaehlerClass_holomorphic D hHodgeDecomposition hg (Θ φ)

theorem nativeThetaClass_component (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) (j : Fin D.pel.componentCount)
    (φ : D.sphericalInputs) :
    (Forms.componentRestriction D hg j).baseChange ℂ (nativeThetaClass D hg Θ φ) =
      ClosedForms.thetaComplexifiedComponent D hg Θ j φ :=
  nativeKaehlerClass_component D hg j (Θ φ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass
