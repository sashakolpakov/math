import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocusPullbackFromAmbient
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.IntersectionMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GluedRankChartIntersections

/-! # Chart Pullbacks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ChartPullbacks

noncomputable section

/-! The product-denominator Hilbert locus is the actual fiber
product of the two Hilbert charts over the glued rank scheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (D : ℕ) (P : Polynomial ℚ)

def stableHilbertChartToRank : Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P ⟶
    Stable.PolynomialRankScheme.stablePolynomialRankOver R (n := n) i D (Stable.ConfigurationLocus.configurationHilbertRank D P) :=
  Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P ≫
    Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D (Stable.ConfigurationLocus.configurationHilbertRank D P) j

instance stableHilbertChartToRank_isImmersion : IsImmersion (stableHilbertChartToRank R i j D P).left := by
  change IsImmersion ((Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P).left ≫
    (Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D (Stable.ConfigurationLocus.configurationHilbertRank D P) j).left)
  infer_instance

instance stableHilbertChartToRank_mono : Mono (stableHilbertChartToRank R i j D P) := Over.mono_of_mono_left _

variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)

theorem stableHilbertIntersectionLeftMap_toRank :
    IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD ≫ stableHilbertChartToRank R i j D P =
      stableHilbertChartToRank R i (j.intersection k) D P := by
  rw [stableHilbertChartToRank, ← Category.assoc, IntersectionMaps.stableHilbertIntersectionLeftMap_factor,
    Category.assoc, GluedRankChartIntersections.stableRankIntersectionLeftMap_toGlued]
  rfl

theorem stableHilbertIntersectionRightMap_toRank :
    IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD ≫ stableHilbertChartToRank R i k D P =
      stableHilbertChartToRank R i (j.intersection k) D P := by
  rw [stableHilbertChartToRank, ← Category.assoc, IntersectionMaps.stableHilbertIntersectionRightMap_factor,
    Category.assoc, GluedRankChartIntersections.stableRankIntersectionRightMap_toGlued]
  rfl

theorem stableHilbertChartIntersection_isPullback :
    IsPullback (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)
      (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD)
      (stableHilbertChartToRank R i j D P) (stableHilbertChartToRank R i k D P) := by
  have : Mono (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD) := Over.mono_of_mono_left _
  have hc := (stableHilbertIntersectionLeftMap_toRank R i j k D P hP hD).trans
    (stableHilbertIntersectionRightMap_toRank R i j k D P hP hD).symm
  let : Mono (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i k D P ≫
      Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D (Stable.ConfigurationLocus.configurationHilbertRank D P) k) :=
    inferInstanceAs (Mono (stableHilbertChartToRank R i k D P))
  exact HilbertScheme.Presentations.LocusPullbackFromAmbient.Construction.locusPullbackFromAmbient
    (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)
    (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD)
    (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i (j.intersection k) D P)
    (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P)
    (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i k D P)
    (Stable.RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P))
    (Stable.RankIntersectionMaps.stableRankIntersectionRightMap R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P))
    (Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D (Stable.ConfigurationLocus.configurationHilbertRank D P) j)
    (Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D (Stable.ConfigurationLocus.configurationHilbertRank D P) k)
    hc (GluedRankChartIntersections.stableRankGluedChartIntersection_isPullback R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P))
    (IntersectionMaps.stableHilbertIntersectionLeft_isPullback R i j k D P hP hD)

include hP hD in
theorem stableHilbertChartPullback_fst_open :
    IsOpenImmersion (pullback.fst (stableHilbertChartToRank R i j D P) (stableHilbertChartToRank R i k D P)).left := by
  let hp := stableHilbertChartIntersection_isPullback R i j k D P hP hD
  have he := congrArg Over.Hom.left hp.isoPullback_inv_fst
  have : IsIso hp.isoPullback.inv.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (.of R))).map hp.isoPullback.inv))
  have hi : IsOpenImmersion (hp.isoPullback.inv.left ≫
      (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD).left) := inferInstance
  change hp.isoPullback.inv.left ≫ (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD).left = _ at he
  rw [he] at hi
  exact hi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ChartPullbacks
