import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaWitness
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaPureForms
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonIntrinsicClass
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Albanese

/-! # Theta Betti Class -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaBettiClass.CM

noncomputable section

/-! The actual GeometricTheta theta lift defines a native Albanese Betti class.
Its Hecke action is the one retained in the full GeometricTheta witness, and its
pullback is the integration-defined class on the chosen ball surface. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (W : ThetaWitness.CM.Witness D hg hq hIsogenyQuotient)

def classMap : D.sphericalInputs →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1 :=
  CMExtraction.Intrinsic.ThetaClass.nativeThetaClass D hg W.theta

def restriction : D.pel.H1 →ₗ[ℚ] W.variety.rationalCohomology 1 :=
  PELModuli.IntegralModel.Product.bettiPullbackQ
    (W.component.hom ≫ D.componentComplexInclusion W.index ≫ D.pel.complexAlbaneseMap hg) 1

theorem holomorphic (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput) (φ : D.sphericalInputs) :
    classMap D hg hq hIsogenyQuotient W φ ∈ (CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg).holomorphic :=
  CMExtraction.Intrinsic.ThetaClass.nativeThetaClass_holomorphic D hHodgeDecomposition hg W.theta φ

theorem covariance (h : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (φ : D.sphericalInputs) :
    D.activeH1Complex W.action W.active h (classMap D hg hq hIsogenyQuotient W φ) =
      classMap D hg hq hIsogenyQuotient W (D.sphericalWeilComplex h φ) :=
  CMExtraction.ComparisonIntrinsicClass.Intrinsic.nativeThetaClass_hecke D hg (CMExtraction.Intrinsic.Albanese.nativeAlbaneseProjectiveOfGeometry D hg) hq hIsogenyQuotient
    W.action W.realization W.forms W.formsPullback W.active W.theta W.covariance h φ

theorem restriction_class (φ : D.sphericalInputs) :
    (restriction D hg hq hIsogenyQuotient W).baseChange ℂ (classMap D hg hq hIsogenyQuotient W φ) =
      ThetaPureForms.CM.betti D hg W.theta W.index W.variety W.component φ := by
  let P := CMExtraction.Intrinsic.Albanese.nativeAlbaneseProjectiveOfGeometry D hg
  change (restriction D hg hq hIsogenyQuotient W).baseChange ℂ (CMExtraction.Intrinsic.ThetaClass.nativeKaehlerClass D hg (W.theta φ)) = _
  rw [CMExtraction.ComparisonIntrinsicClass.Intrinsic.nativeKaehlerClass_eq_projective D hg P]
  have h := CMExtraction.KaehlerClasses.Intrinsic.presentationKaehlerComplexifiedClass_integralPullback W.variety
    (CMExtraction.ComparisonIntrinsicClass.Intrinsic.nativeAlbanesePresentation D hg P)
    (W.component.hom ≫ D.componentComplexInclusion W.index ≫ D.pel.complexAlbaneseMap hg)
    (W.theta φ)
  refine h.symm.trans ?_
  change CMExtraction.KaehlerClasses.Intrinsic.kaehlerComplexifiedClass W.variety
    (AbelianScheme.TateComparison.FormConstants.formsPullback (W.component.hom ≫ D.componentComplexInclusion W.index ≫
      D.pel.complexAlbaneseMap hg) (W.theta φ)) = _
  rw [← Category.assoc, AbelianScheme.TateComparison.FormConstants.formsPullback_comp]
  rfl

theorem restriction_hodge (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg)
      (CMExtraction.Mem.canonicalH1 hHodgeDecomposition W.variety.presentation)
      (restriction D hg hq hIsogenyQuotient W) := by
  let f : W.variety.toOver ⟶ (CMExtraction.Intrinsic.Base.singleBaseSpacePresentation D hg).toOver :=
    W.component.hom ≫ D.componentComplexInclusion W.index ≫ (CMExtraction.Intrinsic.Base.singleBaseSpaceIso D hg).inv
  have h := (CMExtraction.Naturality.canonicalH1_pullback hHodgeDecomposition W.variety.presentation
    (CMExtraction.Intrinsic.Base.singleBaseSpacePresentation D hg) f).comp (CMExtraction.Intrinsic.Base.nativeAlbaneseBettiEquiv_isHodgeMap D hHodgeDecomposition hg)
  have he : (PELModuli.IntegralModel.Product.bettiPullbackQ f 1).comp (CMExtraction.Intrinsic.Base.nativeAlbaneseBettiEquiv D hg).toLinearMap =
      restriction D hg hq hIsogenyQuotient W := by
    rw [CMExtraction.Intrinsic.Base.nativeAlbaneseBettiEquiv_eq_pullback, ← PELModuli.IntegralModel.Product.bettiPullbackQ_comp]
    apply congrArg (fun g => PELModuli.IntegralModel.Product.bettiPullbackQ g 1)
    dsimp only [f, restriction]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact he ▸ h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaBettiClass.CM
