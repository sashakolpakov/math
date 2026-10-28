import OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.InfinityInclusion
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Bundle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealAffineCover

/-! # Infinity Bundle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.InfinityBundle.Cycles

noncomputable section

/-! The actual global conormal infinity hyperplane has an invertible
ideal sheaf, obtained from its cartesian conormal charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} (I : X.IdealSheafData)

theorem globalConormalInfinity_regularPrincipalImageIdeals :
    Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals (InfinityInclusion.BundleCycles.globalConormalInfinityInclusion I) :=
  Cartier.IdealAffineCover.BundleCycles.regularPrincipalImageIdeals_of_openCover (InfinityInclusion.BundleCycles.globalConormalInfinityInclusion I)
    (Conormal.ProjectiveGluing.BundleCycles.globalConormalProjectiveCover I) (Conormal.InfinityDiagram.BundleCycles.conormalInfinityChart I)
    (fun U => (Conormal.InfinityGluing.BundleCycles.globalConormalInfinityCover I).f U)
    (fun U => SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent)
    (InfinityInclusion.BundleCycles.globalConormalInfinityInclusion_chart_isPullback I)
    (fun U => SymmetricInfinity.Bundle.Cycles.symmetricInfinity_regularPrincipalImageIdeals (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent)

def globalConormalInfinityIdealLineBundle : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle (Conormal.ProjectiveGluing.BundleCycles.globalConormalProjective I) :=
  Cartier.IdealBundle.Cycles.cartierIdealLineBundle (InfinityInclusion.BundleCycles.globalConormalInfinityInclusion I)
    (globalConormalInfinity_regularPrincipalImageIdeals I)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.InfinityBundle.Cycles
