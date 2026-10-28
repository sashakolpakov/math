import OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.RankChowEquiv
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.RankChowDetection

/-! # Chow Joint Detection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.ChowJointDetection.BundleCycles

noncomputable section

/-! Genuine conormal fiber extension detects rational equivalence
jointly in all dimension grades, even when its rank varies. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated]
    (p : Y ⟶ X) [Smooth p] (s : X ⟶ Y) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X)
    [Smooth (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker)] [GeometricallyIntegral (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker)]
    (f : s.ker.subscheme ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (h : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker))

include p hs h in
theorem globalConormalPointChow_joint_zero (z : s.ker.subscheme →₀ ℚ)
    (hz : ∀ e : ℕ, Point.CycleChow.BundleCycles.pointCycleToChowQ (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker ≫ f) e
      (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) z) = 0) :
    ∀ d : ℕ, Point.CycleChow.BundleCycles.pointCycleToChowQ f d z = 0 := by
  intro d
  apply AffineBundle.RankChowDetection.Cycles.affineBundleRankChow_joint_zero (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) f h d
  intro r
  let q := Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker
  let U := AffineBundle.FiberRankOpen.Cycles.affineBundleRankOpen q f h r
  let i := U.ι
  let q' := pullback.snd q i
  let j := pullback.fst q i
  have hq : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank q' r := AffineBundle.FiberRankOpen.Cycles.affineBundleRankOpen_charts q f h r
  apply (OpenChowEquiv.BundleCycles.globalConormalOpenChowExtension_bijective p s hs f i r hq d).injective
  rw [map_zero, Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass, AffineBundle.ChowPointClass.Cycles.affineBundleChowExtension_pointClass]
  have he : j ≫ (q ≫ f) = q' ≫ (i ≫ f) := by
    rw [← Category.assoc, pullback.condition, Category.assoc]
  have H := congrArg (fun a => DimensionChow.BundleCycles.dimensionChowTransport he (d + r)
    (Open.ChowRestriction.BundleCycles.openChowRestriction j (q ≫ f) (d + r) a)) (hz (d + r))
  simp only [map_zero] at H
  change DimensionChow.BundleCycles.dimensionChowTransport he (d + r) (Open.ChowRestriction.BundleCycles.openChowRestriction j (q ≫ f) (d + r)
    (Point.CycleChow.BundleCycles.pointCycleToChowQ (q ≫ f) (d + r) (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension q z))) = 0 at H
  rw [Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass, Point.ChowTransport.BundleCycles.dimensionChowTransport_pointCycle] at H
  rw [Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_openSquare q q' i j (pullback.condition.symm)] at H
  exact H

include p hs h in
theorem globalConormalPointChow_joint_equal (z w : s.ker.subscheme →₀ ℚ)
    (hzw : ∀ e : ℕ, Point.CycleChow.BundleCycles.pointCycleToChowQ (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker ≫ f) e
      (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker ≫ f) e
        (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) w)) :
    ∀ d : ℕ, Point.CycleChow.BundleCycles.pointCycleToChowQ f d z = Point.CycleChow.BundleCycles.pointCycleToChowQ f d w := by
  have H := globalConormalPointChow_joint_zero p s hs f h (z - w) (by
    intro e
    rw [map_sub, map_sub, hzw e, sub_self])
  intro d
  exact sub_eq_zero.mp ((map_sub (Point.CycleChow.BundleCycles.pointCycleToChowQ f d) z w).symm.trans (H d))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.ChowJointDetection.BundleCycles
