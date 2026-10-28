import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.CompactificationDiagram
import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.GluedMap

/-! # Compactification -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.Compactification.BundleCycles

noncomputable section

/-! The actual global conormal spectrum embeds into its glued
projective augmented symmetric spectrum, with genuine pullback charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} (I : X.IdealSheafData)

def globalConormalCompactification : Conormal.DiagramGluing.BundleCycles.globalConormalSpectrum I ⟶ Conormal.ProjectiveGluing.BundleCycles.globalConormalProjective I :=
  Relative.GluedMap.BundleCycles.relativeGluedMap (Conormal.DiagramGluing.BundleCycles.conormalSymmetricGlueData I) (Conormal.ProjectiveGluing.BundleCycles.conormalProjectiveGlueData I) (Conormal.CompactificationDiagram.BundleCycles.conormalCompactificationDiagram I)

theorem globalConormalCompactification_on_chart (U : X.AffineZariskiSite) :
    (Conormal.DiagramGluing.BundleCycles.globalConormalSpectrumCover I).f U ≫ globalConormalCompactification I =
      Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent ≫
        (Conormal.ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).f U :=
  Relative.GluedMap.BundleCycles.relativeGluedMap_on_chart _ _ _ U

theorem globalConormalCompactification_toBase :
    globalConormalCompactification I ≫ Conormal.ProjectiveGluing.BundleCycles.globalConormalProjectiveToBase I =
      Conormal.DiagramGluing.BundleCycles.globalConormalSpectrumProjection I :=
  Relative.GluedMap.BundleCycles.relativeGluedMap_toBase _ _ _ (Conormal.CompactificationDiagram.BundleCycles.conormalCompactificationDiagram_over I)

theorem globalConormalCompactification_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback (Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent)
      ((Conormal.DiagramGluing.BundleCycles.globalConormalSpectrumCover I).f U) ((Conormal.ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).f U)
      (globalConormalCompactification I) :=
  Relative.GluedMap.BundleCycles.relativeGluedMap_chart_isPullback _ _ _ (Conormal.CompactificationDiagram.BundleCycles.conormalCompactificationDiagram_over I) U

instance globalConormalCompactification_isOpenImmersion : IsOpenImmersion (globalConormalCompactification I) :=
  Relative.GluedMap.BundleCycles.relativeGluedMap_morphismProperty _ _ _ (Conormal.CompactificationDiagram.BundleCycles.conormalCompactificationDiagram_over I) (@IsOpenImmersion)
    (fun _U => Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification_isOpenImmersion _ _)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.Compactification.BundleCycles
