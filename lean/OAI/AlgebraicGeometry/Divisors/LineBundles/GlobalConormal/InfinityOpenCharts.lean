import OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.InfinityRankAtPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ChartsOpenBaseChange

/-! # Infinity Open Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.InfinityOpenCharts.BundleCycles

noncomputable section

/-! Over any open subset of positive constant affine conormal rank,
the actual infinity pullback has free infinity charts of one lower rank. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {X Y U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y]
    (p : Y ⟶ X) [Smooth p] (s : X ⟶ Y) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X)
    (f : s.ker.subscheme ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (i : U ⟶ s.ker.subscheme) [IsOpenImmersion i] (r : ℕ)
    (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (pullback.snd (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) i) (r + 1))

include p hs f hq in
theorem globalConormalInfinity_openBaseChange_hasFreeChartsOfRank :
    Free.InfinityCharts.BundleCycles.HasFreeProjectiveInfinityChartsOfRank (pullback.snd (Conormal.InfinitySupport.BundleCycles.globalConormalInfinityToSupport s.ker) i)
      (((InfinityBundle.Cycles.globalConormalInfinityIdealLineBundle s.ker).pullback (InfinityInclusion.BundleCycles.globalConormalInfinityInclusion s.ker)).pullback
        (pullback.fst (Conormal.InfinitySupport.BundleCycles.globalConormalInfinityToSupport s.ker) i)) r := by
  have HP := FreeInfinityCharts.BundleCycles.globalConormal_hasFreeInfinityCharts p s hs
  let : GeometricallyIntegral (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker) := Free.InfinityCharts.BundleCycles.freeInfinityCharts_geometricallyIntegral _ _ HP
  have HQ := Affine.SpaceChartBaseChange.BundleCycles.hasAffineSpaceCharts_of_specCharts (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker)
    (Global.SectionAffineSpaceCharts.BundleCycles.globalSection_exists_affineSpaceChart p s hs)
  let : GeometricallyIntegral (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) := HQ.geometricallyIntegral
  let : AlgebraicGeometry.IsNoetherian U := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian i
  let : AlgebraicGeometry.IsNoetherian (pullback (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) i : Scheme) :=
    Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian (pullback.fst (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) i)
  apply Free.ChartsOpenBaseChange.BundleCycles.freeInfinityCharts_openBaseChange_of_rank _ _ i r
  intro u
  apply InfinityRankAtPoint.BundleCycles.globalConormalInfinity_hasFreeChart_of_fiberRank p s hs f r (i u)
  rw [AffineBundle.FiberRankOpen.Cycles.affineBundleFiberRank_openSquare (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker)
    (pullback.snd (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) i) i (pullback.fst (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) i)
    (pullback.condition.symm) f u]
  exact AffineBundle.FiberRank.Cycles.affineBundleFiberRank_eq_of_rank _ (i ≫ f) (r + 1) hq u

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.InfinityOpenCharts.BundleCycles
