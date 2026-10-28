import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.PolynomialRankScheme

/-! # Glued Rank Chart Intersections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GluedRankChartIntersections

noncomputable section

/-! The original product-denominator rank intersections remain
the actual intersections after the rank charts are glued. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable (R : Type u) [CommRing R] {n m : ℕ} (i : Fin m)
variable (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (D q : ℕ)

instance stablePolynomialRankChartOver_open : IsOpenImmersion (Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D q j).left :=
  Stable.PolynomialRankScheme.stablePolynomialRankChart_open R i D q j

theorem stableRankIntersectionLeftMap_toGlued :
    Stable.RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D q ≫ Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D q j =
      Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D q (j.intersection k) := by
  apply (cancel_mono (Stable.PolynomialRankScheme.stablePolynomialRankParameterOver R i D q)).mp
  rw [Category.assoc, Stable.PolynomialRankScheme.stablePolynomialRankChartOver_parameter, Stable.PolynomialRankScheme.stablePolynomialRankChartOver_parameter]
  exact Stable.RankChartsOverBase.stableRankIntersectionLeftMap_toStable R i j k D q

theorem stableRankIntersectionRightMap_toGlued :
    Stable.RankIntersectionMaps.stableRankIntersectionRightMap R i j k D q ≫ Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D q k =
      Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D q (j.intersection k) := by
  apply (cancel_mono (Stable.PolynomialRankScheme.stablePolynomialRankParameterOver R i D q)).mp
  rw [Category.assoc, Stable.PolynomialRankScheme.stablePolynomialRankChartOver_parameter, Stable.PolynomialRankScheme.stablePolynomialRankChartOver_parameter]
  exact Stable.RankChartsOverBase.stableRankIntersectionRightMap_toStable R i j k D q

theorem stableRankGluedChartIntersection_isPullback :
    IsPullback (Stable.RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D q) (Stable.RankIntersectionMaps.stableRankIntersectionRightMap R i j k D q)
      (Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D q j) (Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D q k) := by
  let hp := Stable.RankChartPullbacks.stableRankChartIntersection_isPullback R i j k D q
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfFactors _ _ (Stable.PolynomialRankScheme.stablePolynomialRankParameterOver R i D q)
    (Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D q j) (Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D q k)
    (Stable.PolynomialRankScheme.stablePolynomialRankChartOver_parameter R i D q j) (Stable.PolynomialRankScheme.stablePolynomialRankChartOver_parameter R i D q k)
    hp.cone hp.isLimit)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GluedRankChartIntersections
