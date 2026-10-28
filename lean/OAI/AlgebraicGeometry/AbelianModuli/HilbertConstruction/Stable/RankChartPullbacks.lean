import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankChartsOverBase

/-! # Rank Chart Pullbacks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankChartPullbacks

noncomputable section

/-! The product-denominator rank locus is the actual fiber product
of the two rank charts over the stable configuration open. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable (R : Type u) [CommRing R] {n m : ℕ} (i : Fin m)
variable (j k : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (D q : ℕ)

instance stableConfigurationPolynomialRankInclusion_mono :
    Mono (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D q) :=
  Over.mono_of_mono_left _

instance stableBalancedAffineChartOverMap_open :
    IsOpenImmersion (RankChartsOverBase.stableBalancedAffineChartOverMap R i j).left :=
  BalancedAffineCover.stableBalancedAffineChartMap_open R i j

instance stableRankChartToStable_isImmersion :
    IsImmersion (RankChartsOverBase.stableRankChartToStable R i j D q).left := by
  change IsImmersion ((ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D q).left ≫
    (RankChartsOverBase.stableBalancedAffineChartOverMap R i j).left)
  infer_instance

instance stableRankChartToStable_mono : Mono (RankChartsOverBase.stableRankChartToStable R i j D q) :=
  Over.mono_of_mono_left _

theorem stableRankChartIntersection_isPullback :
    IsPullback (RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D q)
      (RankIntersectionMaps.stableRankIntersectionRightMap R i j k D q)
      (RankChartsOverBase.stableRankChartToStable R i j D q) (RankChartsOverBase.stableRankChartToStable R i k D q) := by
  have : Mono (RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D q) := Over.mono_of_mono_left _
  have hc := (RankChartsOverBase.stableRankIntersectionLeftMap_toStable R i j k D q).trans
    (RankChartsOverBase.stableRankIntersectionRightMap_toStable R i j k D q).symm
  apply IsPullback.mk'
  · exact hc
  · intro T f g h _
    exact (cancel_mono (RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D q)).mp h
  · intro T f g h
    let hp := RankChartsOverBase.stableChartIntersectionOver_isPullback R i j k
    have ha : (f ≫ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D q) ≫
        RankChartsOverBase.stableBalancedAffineChartOverMap R i j =
        (g ≫ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i k D q) ≫
          RankChartsOverBase.stableBalancedAffineChartOverMap R i k := by
      simpa only [RankChartsOverBase.stableRankChartToStable, Category.assoc] using h
    let x := hp.lift (f ≫ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D q)
      (g ≫ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i k D q) ha
    have hx : x ≫ StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k =
        f ≫ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D q := hp.lift_fst _ _ ha
    have hl : IsPullback (RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D q)
        (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i (j.intersection k) D q)
        (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D q)
        (StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k) := by
      apply IsPullback.of_map_of_faithful (Over.forget (Spec (.of R)))
      exact RankIntersectionMaps.stableRankIntersectionLeft_isPullback R i j k D q
    let y := hl.lift f x hx.symm
    have hy : y ≫ RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D q = f := hl.lift_fst _ _ hx.symm
    refine ⟨y, hy, ?_⟩
    apply (cancel_mono (RankChartsOverBase.stableRankChartToStable R i k D q)).mp
    rw [Category.assoc, ← hc, ← Category.assoc, hy]
    exact h

instance stableRankChartPullback_fst_open :
    IsOpenImmersion (pullback.fst (RankChartsOverBase.stableRankChartToStable R i j D q)
      (RankChartsOverBase.stableRankChartToStable R i k D q)).left := by
  let hp := stableRankChartIntersection_isPullback R i j k D q
  have he := congrArg Over.Hom.left hp.isoPullback_inv_fst
  have : IsIso hp.isoPullback.inv.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (.of R))).map hp.isoPullback.inv))
  have hi : IsOpenImmersion (hp.isoPullback.inv.left ≫
      (RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D q).left) := inferInstance
  change hp.isoPullback.inv.left ≫ (RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D q).left = _ at he
  rw [he] at hi
  exact hi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankChartPullbacks
