import OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.OpenChowEquiv
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.FiberRankOpen

/-! # Rank Chow Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.RankChowEquiv.BundleCycles

noncomputable section

/-! Every actual conormal rank stratum has a Chow equivalence in
all dimension grades, with no global rank or purity hypothesis. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated]
    (p : Y ⟶ X) [Smooth p] (s : X ⟶ Y) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X)
    [Smooth (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker)] [GeometricallyIntegral (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker)]
    (f : s.ker.subscheme ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (h : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker)) (r : ℕ)

include p hs in
theorem globalConormalRankChowExtension_bijective (d : ℕ) :
    Function.Bijective (AffineBundle.ChowExtension.Cycles.affineBundleChowExtension
      (pullback.snd (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) (AffineBundle.FiberRankOpen.Cycles.affineBundleRankOpen (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) f h r).ι)
      ((AffineBundle.FiberRankOpen.Cycles.affineBundleRankOpen (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) f h r).ι ≫ f) r
      (AffineBundle.FiberRankOpen.Cycles.affineBundleRankOpen_charts (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) f h r) d) :=
  OpenChowEquiv.BundleCycles.globalConormalOpenChowExtension_bijective p s hs f
    (AffineBundle.FiberRankOpen.Cycles.affineBundleRankOpen (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) f h r).ι r
    (AffineBundle.FiberRankOpen.Cycles.affineBundleRankOpen_charts (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) f h r) d

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.RankChowEquiv.BundleCycles
