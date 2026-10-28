import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AmbientPullback

/-! # Lift Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LiftRecovery

noncomputable section

/-! The glued Hilbert parameter recovers the exact Hilbert
lifting condition on every rank chart, for arbitrary test schemes. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)

theorem stableHilbert_chart_lift_iff (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (T : Over (Spec (.of R)))
    (x : T ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D (Stable.ConfigurationLocus.configurationHilbertRank D P)) :
    (∃! a : T ⟶ Scheme.stableHilbertOver R i D P hP hD,
      a ≫ Scheme.stableHilbertRankParameterOver R i D P hP hD =
        x ≫ Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D (Stable.ConfigurationLocus.configurationHilbertRank D P) j) ↔
    (∃! a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P,
      a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P = x) := by
  constructor
  · rintro ⟨a, ha, _⟩
    let hp := AmbientPullback.stableHilbertChartOver_isPullback R i D P hP hD j
    let b := hp.lift a x ha
    have hb : b ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P = x := hp.lift_snd _ _ ha
    exact ⟨b, hb, fun c hc => (cancel_mono (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P)).mp
      (hc.trans hb.symm)⟩
  · rintro ⟨a, ha, _⟩
    have hb : (a ≫ Scheme.stableHilbertChartOver R i D P hP hD j) ≫ Scheme.stableHilbertRankParameterOver R i D P hP hD =
        x ≫ Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D (Stable.ConfigurationLocus.configurationHilbertRank D P) j := by
      rw [Category.assoc, Scheme.stableHilbertChartOver_rankParameter]
      change a ≫ (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P ≫ _) = _
      rw [← Category.assoc, ha]
    exact ⟨a ≫ Scheme.stableHilbertChartOver R i D P hP hD j, hb,
      fun c hc => (cancel_mono (Scheme.stableHilbertRankParameterOver R i D P hP hD)).mp (hc.trans hb.symm)⟩

def stableHilbertParameterToStable : Scheme.stableHilbertOver R i D P hP hD ⟶
    Stable.BalancedProjectiveOpen.stableBalancedQuotientScheme R (r := n + 1) i :=
  Scheme.stableHilbertRankParameterOver R i D P hP hD ≫
    Stable.PolynomialRankScheme.stablePolynomialRankParameterOver R (n := n) i D (Stable.ConfigurationLocus.configurationHilbertRank D P)

instance stableHilbertParameterToStable_mono : Mono (stableHilbertParameterToStable R i D P hP hD) := by
  unfold stableHilbertParameterToStable
  infer_instance

theorem stableHilbertChartOver_toStable (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    Scheme.stableHilbertChartOver R i D P hP hD j ≫ stableHilbertParameterToStable R i D P hP hD =
      Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P ≫
        Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D (Stable.ConfigurationLocus.configurationHilbertRank D P) ≫
          Stable.RankChartsOverBase.stableBalancedAffineChartOverMap R i j := by
  rw [stableHilbertParameterToStable, ← Category.assoc, Scheme.stableHilbertChartOver_rankParameter]
  change (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P ≫
    Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D (Stable.ConfigurationLocus.configurationHilbertRank D P) j) ≫ _ = _
  rw [Category.assoc, Stable.PolynomialRankScheme.stablePolynomialRankChartOver_parameter]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LiftRecovery
