import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.Scheme

/-! # Ambient Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AmbientPullback

noncomputable section

/-! Each rank chart pulls the glued Hilbert scheme back to its
original Hilbert locus, with the full scheme structure. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)

theorem stableHilbertIntersection_chart_condition
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD).left ≫ StableHilbert.Scheme.stableHilbertChart R i D P hP hD j =
      (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD).left ≫ StableHilbert.Scheme.stableHilbertChart R i D P hP hD k := by
  apply (cancel_mono (StableHilbert.Scheme.stableHilbertRankParameter R i D P hP hD)).mp
  rw [Category.assoc, Category.assoc, StableHilbert.Scheme.stableHilbertChart_rankParameter, StableHilbert.Scheme.stableHilbertChart_rankParameter]
  exact congrArg Over.Hom.left ((ChartPullbacks.stableHilbertIntersectionLeftMap_toRank R i j k D P hP hD).trans
    (ChartPullbacks.stableHilbertIntersectionRightMap_toRank R i j k D P hP hD).symm)

theorem stableHilbertChart_preimage (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    (StableHilbert.Scheme.stableHilbertRankParameter R i D P hP hD) ⁻¹ᵁ
        (Stable.PolynomialRankScheme.stablePolynomialRankChart R i D (Stable.ConfigurationLocus.configurationHilbertRank D P) j).opensRange =
      (StableHilbert.Scheme.stableHilbertChart R i D P hP hD j).opensRange := by
  ext x
  change StableHilbert.Scheme.stableHilbertRankParameter R i D P hP hD x ∈
    Set.range (Stable.PolynomialRankScheme.stablePolynomialRankChart R i D (Stable.ConfigurationLocus.configurationHilbertRank D P) j) ↔
      x ∈ Set.range (StableHilbert.Scheme.stableHilbertChart R i D P hP hD j)
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨k, y, rfl⟩ := StableHilbert.Scheme.stableHilbertCharts_cover R i D P hP hD x
    have he : Stable.PolynomialRankScheme.stablePolynomialRankChart R i D (Stable.ConfigurationLocus.configurationHilbertRank D P) j v =
        Stable.PolynomialRankScheme.stablePolynomialRankChart R i D (Stable.ConfigurationLocus.configurationHilbertRank D P) k
          ((Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i k D P).left y) := by
      rw [hv, ← Scheme.Hom.comp_apply, StableHilbert.Scheme.stableHilbertChart_rankParameter]
      rfl
    obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback
      ((GluedRankChartIntersections.stableRankGluedChartIntersection_isPullback R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P)).map
        (Over.forget (Spec (.of R)))) v ((Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i k D P).left y) he
    obtain ⟨t, ht, _⟩ := Scheme.exists_preimage_of_isPullback
      ((IntersectionMaps.stableHilbertIntersectionRight_isPullback R i j k D P hP hD).map (Over.forget (Spec (.of R)))) y z hz.symm
    refine ⟨(IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD).left t, ?_⟩
    change (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD).left t = y at ht
    have hc := congrArg (fun h => h t) (stableHilbertIntersection_chart_condition R i D P hP hD j k)
    simpa only [Scheme.Hom.comp_apply, ht] using hc
  · rintro ⟨y, rfl⟩
    refine ⟨(Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P).left y, ?_⟩
    exact (congrArg (fun h => h y) (StableHilbert.Scheme.stableHilbertChart_rankParameter R i D P hP hD j)).symm

theorem stableHilbertChart_isPullback (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    IsPullback (StableHilbert.Scheme.stableHilbertChart R i D P hP hD j)
      (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P).left
      (StableHilbert.Scheme.stableHilbertRankParameter R i D P hP hD)
      (Stable.PolynomialRankScheme.stablePolynomialRankChart R i D (Stable.ConfigurationLocus.configurationHilbertRank D P) j) :=
  (IsOpenImmersion.isPullback (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P).left
    (StableHilbert.Scheme.stableHilbertChart R i D P hP hD j) (Stable.PolynomialRankScheme.stablePolynomialRankChart R i D (Stable.ConfigurationLocus.configurationHilbertRank D P) j)
    (StableHilbert.Scheme.stableHilbertRankParameter R i D P hP hD) (StableHilbert.Scheme.stableHilbertChart_rankParameter R i D P hP hD j)
    (stableHilbertChart_preimage R i D P hP hD j)).flip

theorem stableHilbertChartOver_isPullback (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    IsPullback (StableHilbert.Scheme.stableHilbertChartOver R i D P hP hD j)
      (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P)
      (StableHilbert.Scheme.stableHilbertRankParameterOver R i D P hP hD)
      (Stable.PolynomialRankScheme.stablePolynomialRankChartOver R i D (Stable.ConfigurationLocus.configurationHilbertRank D P) j) := by
  apply IsPullback.of_map_of_faithful (Over.forget (Spec (.of R)))
  exact stableHilbertChart_isPullback R i D P hP hD j

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AmbientPullback
