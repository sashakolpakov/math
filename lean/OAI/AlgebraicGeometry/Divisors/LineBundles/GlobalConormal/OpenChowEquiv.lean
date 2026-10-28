import OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.InfinityOpenCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.OpenBaseChangeChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.RankZeroChow

/-! # Open Chow Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.OpenChowEquiv.BundleCycles

noncomputable section

/-! The actual conormal Chow equivalence on every open base of
specified constant rank, without a global rank assumption. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {X Y U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated]
    (p : Y ⟶ X) [Smooth p] (s : X ⟶ Y) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X)
    (f : s.ker.subscheme ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (i : U ⟶ s.ker.subscheme) [IsOpenImmersion i]

variable [AlgebraicGeometry.IsNoetherian U]
    [AlgebraicGeometry.IsNoetherian (pullback (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) i : Scheme)]
    [Smooth (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker)] [GeometricallyIntegral (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker)]

variable (r : ℕ) (hq : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank (pullback.snd (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) i) r)

include p hs in
theorem globalConormalOpenChowExtension_bijective (d : ℕ) :
    Function.Bijective (AffineBundle.ChowExtension.Cycles.affineBundleChowExtension (pullback.snd (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) i) (i ≫ f) r hq d) := by
  let : U.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  cases r with
  | zero =>
    let : (pullback (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) i : Scheme).IsSeparated :=
      ⟨by rw [← terminal.comp_from (pullback.fst (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) i)]; infer_instance⟩
    exact AffineBundle.RankZeroChow.Cycles.affineBundleChowExtension_rankZero_bijective _ (i ≫ f) hq d
  | succ r =>
    have HP := FreeInfinityCharts.BundleCycles.globalConormal_hasFreeInfinityCharts p s hs
    let : Smooth (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker) := Free.InfinityCharts.BundleCycles.freeInfinityCharts_smooth _ _ HP
    let : GeometricallyIntegral (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker) := Free.InfinityCharts.BundleCycles.freeInfinityCharts_geometricallyIntegral _ _ HP
    have HD := InfinityOpenCharts.BundleCycles.globalConormalInfinity_openBaseChange_hasFreeChartsOfRank p s hs f i r hq.sourceCharts
    exact Affine.OpenBaseChangeChow.BundleCycles.affineCompactification_openBaseChange_Chow_bijective (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker)
      (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) (Conormal.InfinitySupport.BundleCycles.globalConormalInfinityToSupport s.ker)
      (InfinityInclusion.BundleCycles.globalConormalInfinityInclusion s.ker) (InfinityBoundary.BundleCycles.globalConormalInfinityInclusion_toSupport s.ker)
      (Compactification.BundleCycles.globalConormalCompactification s.ker) (Conormal.ProjectiveProper.BundleCycles.globalConormalCompactification_toSupport s.ker)
      (InfinityBoundary.BundleCycles.globalConormalInfinityInclusion_range s.ker) (InfinityBundle.Cycles.globalConormalInfinityIdealLineBundle s.ker)
      HP i f r HD hq d

def globalConormalOpenChowEquiv (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ (i ≫ f) d ≃ₗ[ℚ]
      DimensionChow.BundleCycles.DimensionChowQ (pullback.snd (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) i ≫ (i ≫ f)) (d + r) :=
  LinearEquiv.ofBijective (AffineBundle.ChowExtension.Cycles.affineBundleChowExtension (pullback.snd (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) i) (i ≫ f) r hq d)
    (globalConormalOpenChowExtension_bijective p s hs f i r hq d)

theorem globalConormalOpenChowEquiv_pointClass (d : ℕ) (z : U →₀ ℚ) :
    globalConormalOpenChowEquiv p s hs f i r hq d (Point.CycleChow.BundleCycles.pointCycleToChowQ (i ≫ f) d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (pullback.snd (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) i ≫ (i ≫ f)) (d + r)
        (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (pullback.snd (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) i) z) :=
  AffineBundle.ChowPointClass.Cycles.affineBundleChowExtension_pointClass _ (i ≫ f) r hq d z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.OpenChowEquiv.BundleCycles
