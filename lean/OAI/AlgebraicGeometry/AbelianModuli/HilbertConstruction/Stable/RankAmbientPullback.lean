import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.PolynomialRankScheme

/-! # Rank Ambient Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankAmbientPullback

noncomputable section

/-! Pulling the glued rank scheme back to an ambient stable chart
recovers exactly that chart's matrix rank locus. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {n m : ℕ} (i : Fin m) (D q : ℕ)

theorem stableRankIntersection_chart_condition
    (j k : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    (RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D q).left ≫ PolynomialRankScheme.stablePolynomialRankChart R i D q j =
      (RankIntersectionMaps.stableRankIntersectionRightMap R i j k D q).left ≫ PolynomialRankScheme.stablePolynomialRankChart R i D q k := by
  apply (cancel_mono (PolynomialRankScheme.stablePolynomialRankParameter R i D q)).mp
  rw [Category.assoc, Category.assoc, PolynomialRankScheme.stablePolynomialRankChart_parameter,
    PolynomialRankScheme.stablePolynomialRankChart_parameter]
  exact congrArg Over.Hom.left
    ((RankChartsOverBase.stableRankIntersectionLeftMap_toStable R i j k D q).trans
      (RankChartsOverBase.stableRankIntersectionRightMap_toStable R i j k D q).symm)

theorem stablePolynomialRankChart_preimage
    (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    (PolynomialRankScheme.stablePolynomialRankParameter R i D q) ⁻¹ᵁ (BalancedAffineCover.stableBalancedAffineChartMap R i j).opensRange =
      (PolynomialRankScheme.stablePolynomialRankChart R i D q j).opensRange := by
  ext x
  change PolynomialRankScheme.stablePolynomialRankParameter R i D q x ∈ Set.range (BalancedAffineCover.stableBalancedAffineChartMap R i j) ↔
    x ∈ Set.range (PolynomialRankScheme.stablePolynomialRankChart R i D q j)
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨k, y, rfl⟩ := PolynomialRankScheme.stablePolynomialRankCharts_cover R i D q x
    have he : BalancedAffineCover.stableBalancedAffineChartMap R i j v =
        BalancedAffineCover.stableBalancedAffineChartMap R i k ((ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i k D q).left y) := by
      rw [hv, ← Scheme.Hom.comp_apply, PolynomialRankScheme.stablePolynomialRankChart_parameter]
      rfl
    obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback
      (BalancedChartPullbacks.stableBalancedChartIntersection_isPullback R i j k) v
      ((ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i k D q).left y) he
    obtain ⟨t, ht, _⟩ := Scheme.exists_preimage_of_isPullback
      (RankIntersectionMaps.stableRankIntersectionRight_isPullback R i j k D q) y z hz.symm
    refine ⟨(RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D q).left t, ?_⟩
    have hc := congrArg (fun h => h t) (stableRankIntersection_chart_condition R i D q j k)
    simpa only [Scheme.Hom.comp_apply, ht] using hc
  · rintro ⟨y, rfl⟩
    refine ⟨(ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D q).left y, ?_⟩
    exact (congrArg (fun h => h y) (PolynomialRankScheme.stablePolynomialRankChart_parameter R i D q j)).symm

theorem stablePolynomialRankChart_isPullback
    (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    IsPullback (PolynomialRankScheme.stablePolynomialRankChart R i D q j)
      (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D q).left
      (PolynomialRankScheme.stablePolynomialRankParameter R i D q) (BalancedAffineCover.stableBalancedAffineChartMap R i j) :=
  by
    have : IsOpenImmersion (BalancedAffineCover.stableBalancedAffineChartMap R i j) :=
      BalancedAffineCover.stableBalancedAffineChartMap_open R i j
    exact (IsOpenImmersion.isPullback (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D q).left
    (PolynomialRankScheme.stablePolynomialRankChart R i D q j) (BalancedAffineCover.stableBalancedAffineChartMap R i j)
    (PolynomialRankScheme.stablePolynomialRankParameter R i D q) (PolynomialRankScheme.stablePolynomialRankChart_parameter R i D q j)
    (stablePolynomialRankChart_preimage R i D q j)).flip

theorem stablePolynomialRankChartOver_isPullback
    (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    IsPullback (PolynomialRankScheme.stablePolynomialRankChartOver R i D q j)
      (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D q)
      (PolynomialRankScheme.stablePolynomialRankParameterOver R i D q) (RankChartsOverBase.stableBalancedAffineChartOverMap R i j) := by
  apply IsPullback.of_map_of_faithful (Over.forget (Spec (.of R)))
  exact stablePolynomialRankChart_isPullback R i D q j

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankAmbientPullback
