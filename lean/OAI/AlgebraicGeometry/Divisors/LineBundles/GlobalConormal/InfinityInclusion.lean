import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityInclusionDiagram
import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.GluedMap

/-! # Infinity Inclusion -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.InfinityInclusion.BundleCycles

noncomputable section

/-! The actual global infinity hyperplane is a closed subscheme of the
glued projective augmented symmetric spectrum, with genuine pullback charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} (I : X.IdealSheafData)

def globalConormalInfinityInclusion : Conormal.InfinityGluing.BundleCycles.globalConormalInfinity I ⟶ Conormal.ProjectiveGluing.BundleCycles.globalConormalProjective I :=
  Relative.GluedMap.BundleCycles.relativeGluedMap (Conormal.InfinityGluing.BundleCycles.conormalInfinityGlueData I) (Conormal.ProjectiveGluing.BundleCycles.conormalProjectiveGlueData I) (Conormal.InfinityInclusionDiagram.BundleCycles.conormalInfinityInclusionDiagram I)

theorem globalConormalInfinityInclusion_on_chart (U : X.AffineZariskiSite) :
    (Conormal.InfinityGluing.BundleCycles.globalConormalInfinityCover I).f U ≫ globalConormalInfinityInclusion I =
      SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent ≫
        (Conormal.ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).f U :=
  Relative.GluedMap.BundleCycles.relativeGluedMap_on_chart _ _ _ U

theorem globalConormalInfinityInclusion_toBase :
    globalConormalInfinityInclusion I ≫ Conormal.ProjectiveGluing.BundleCycles.globalConormalProjectiveToBase I =
      Conormal.InfinityGluing.BundleCycles.globalConormalInfinityToBase I :=
  Relative.GluedMap.BundleCycles.relativeGluedMap_toBase _ _ _ (Conormal.InfinityInclusionDiagram.BundleCycles.conormalInfinityInclusionDiagram_over I)

theorem globalConormalInfinityInclusion_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback (SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent)
      ((Conormal.InfinityGluing.BundleCycles.globalConormalInfinityCover I).f U) ((Conormal.ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).f U)
      (globalConormalInfinityInclusion I) :=
  Relative.GluedMap.BundleCycles.relativeGluedMap_chart_isPullback _ _ _ (Conormal.InfinityInclusionDiagram.BundleCycles.conormalInfinityInclusionDiagram_over I) U

instance globalConormalInfinityInclusion_isClosedImmersion : IsClosedImmersion (globalConormalInfinityInclusion I) :=
  Relative.GluedMap.BundleCycles.relativeGluedMap_morphismProperty _ _ _ (Conormal.InfinityInclusionDiagram.BundleCycles.conormalInfinityInclusionDiagram_over I) (@IsClosedImmersion)
    (fun _U => SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion_isClosedImmersion _ _)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.InfinityInclusion.BundleCycles
