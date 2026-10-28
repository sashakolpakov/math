import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.SupportCover
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.PrincipalChart

/-! # Support Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.SupportPullback.BundleCycles

noncomputable section

/-! # LineBundleCycles: the conormal projection has the actual expected affine and principal chart pullbacks -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} (I : X.IdealSheafData) (U : X.AffineZariskiSite)

theorem globalConormalToSupport_chart_isPullback :
    IsPullback (SupportCover.BundleCycles.conormalChartProjection I U) ((DiagramGluing.BundleCycles.globalConormalSpectrumCover I).f U)
      (Support.Projection.BundleCycles.supportCoefficientChart I U) (SupportCover.BundleCycles.globalConormalToSupport I) := by
  apply IsOpenImmersion.isPullback
  · exact SupportCover.BundleCycles.globalConormalToSupport_on_chart I U
  · exact SupportCover.BundleCycles.globalConormalToSupport_preimage I U

def conormalPrincipalChartToSupport (r : Γ(X, U.1) ⧸ I.ideal U) :
    Spec (.of (Localization.Away r)) ⟶ I.subscheme :=
  Spec.map (CommRingCat.ofHom (algebraMap (Γ(X, U.1) ⧸ I.ideal U) (Localization.Away r))) ≫
    Support.Projection.BundleCycles.supportCoefficientChart I U

def conormalPrincipalChartInclusion (r : Γ(X, U.1) ⧸ I.ideal U) :
    Spec (.of (Symmetric.LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra (I.ideal U).Cotangent (Submonoid.powers r))) ⟶
      DiagramGluing.BundleCycles.globalConormalSpectrum I :=
  Symmetric.PrincipalChart.BundleCycles.symmetricPrincipalChartInclusion (I.ideal U).Cotangent r ≫ (DiagramGluing.BundleCycles.globalConormalSpectrumCover I).f U

instance conormalPrincipalChartToSupport_isOpenImmersion (r : Γ(X, U.1) ⧸ I.ideal U) :
    IsOpenImmersion (conormalPrincipalChartToSupport I U r) := by
  dsimp [conormalPrincipalChartToSupport]
  have h₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Γ(X, U.1) ⧸ I.ideal U) (Localization.Away r)))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of (Γ(X, U.1) ⧸ I.ideal U)) r
  exact @IsOpenImmersion.comp _ _ _ (Spec.map (CommRingCat.ofHom
    (algebraMap (Γ(X, U.1) ⧸ I.ideal U) (Localization.Away r)))) (Support.Projection.BundleCycles.supportCoefficientChart I U)
    h₁ (Support.Projection.BundleCycles.supportCoefficientChart_isOpenImmersion I U)

instance conormalPrincipalChartInclusion_isOpenImmersion (r : Γ(X, U.1) ⧸ I.ideal U) :
    IsOpenImmersion (conormalPrincipalChartInclusion I U r) := by
  dsimp [conormalPrincipalChartInclusion]
  exact @IsOpenImmersion.comp _ _ _ (Symmetric.PrincipalChart.BundleCycles.symmetricPrincipalChartInclusion (I.ideal U).Cotangent r)
    ((DiagramGluing.BundleCycles.globalConormalSpectrumCover I).f U)
    (Symmetric.PrincipalChart.BundleCycles.symmetricPrincipalChartInclusion_isOpenImmersion (I.ideal U).Cotangent r)
    (SupportCover.BundleCycles.globalConormalSpectrumCover_isOpenImmersion I U)

theorem conormalPrincipalChart_isPullback (r : Γ(X, U.1) ⧸ I.ideal U) :
    IsPullback (Symmetric.PrincipalChart.BundleCycles.symmetricPrincipalChartProjection (I.ideal U).Cotangent r)
      (conormalPrincipalChartInclusion I U r)
      (conormalPrincipalChartToSupport I U r) (SupportCover.BundleCycles.globalConormalToSupport I) := by
  exact (Symmetric.PrincipalChart.BundleCycles.symmetricPrincipalChart_isPullback (I.ideal U).Cotangent r).flip.paste_vert
    (globalConormalToSupport_chart_isPullback I U)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.SupportPullback.BundleCycles
