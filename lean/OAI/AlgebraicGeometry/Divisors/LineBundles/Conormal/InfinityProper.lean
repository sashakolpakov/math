import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinitySupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ProjectiveProper

/-! # Infinity Proper -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityProper.BundleCycles

noncomputable section

/-! Over a locally noetherian ambient scheme, the actual infinity
hyperplane is proper over the closed center. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [hX : IsLocallyNoetherian X] (I : X.IdealSheafData)

include hX

instance globalConormalInfinityToSupport_isProper : IsProper (InfinitySupport.BundleCycles.globalConormalInfinityToSupport I) := by
  apply Global.DeformationProperties.BundleCycles.morphismProperty_of_cover_pullbacks (@IsProper) (InfinitySupport.BundleCycles.globalConormalInfinityToSupport I)
    I.subschemeCover.openCover (InfinityDiagram.BundleCycles.conormalInfinityChart I)
    (fun U => (InfinityGluing.BundleCycles.globalConormalInfinityCover I).f U)
    (fun U => (InfinityGluing.BundleCycles.conormalInfinityToCoefficients I).app U)
    (InfinitySupport.BundleCycles.globalConormalInfinityToSupport_chart_isPullback I)
  intro U
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
  let : Module.Finite (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent := ProjectiveProper.BundleCycles.cotangentQuotient_finite _
  exact SymmetricProjective.Proper.BundleCycles.symmetricProjectiveToBase_isProper _ _

instance globalConormalInfinityToBase_isProper : IsProper (InfinityGluing.BundleCycles.globalConormalInfinityToBase I) := by
  rw [← InfinitySupport.BundleCycles.globalConormalInfinityToSupport_toBase]
  infer_instance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityProper.BundleCycles
