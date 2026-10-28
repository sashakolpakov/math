import OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.InfinityBundle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealPullbackIso

/-! # Infinity Chart Ideal -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityChartIdeal.BundleCycles

noncomputable section

/-! The actual global infinity ideal restricts to the actual
symmetric infinity ideal on each conormal projective chart. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} (I : X.IdealSheafData) (U : X.AffineZariskiSite)

def conormalInfinityChartIdealIso :
    ((GlobalConormal.InfinityBundle.Cycles.globalConormalInfinityIdealLineBundle I).pullback ((ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I).f U)).sheaf ≅
      (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent).sheaf :=
  Cartier.IdealPullbackIso.BundleCycles.cartierIdealPullbackIso (GlobalConormal.InfinityInclusion.BundleCycles.globalConormalInfinityInclusion I)
    (SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent)
    _ _ (GlobalConormal.InfinityInclusion.BundleCycles.globalConormalInfinityInclusion_chart_isPullback I U)
    (GlobalConormal.InfinityBundle.Cycles.globalConormalInfinity_regularPrincipalImageIdeals I)
    (SymmetricInfinity.Bundle.Cycles.symmetricInfinity_regularPrincipalImageIdeals (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityChartIdeal.BundleCycles
