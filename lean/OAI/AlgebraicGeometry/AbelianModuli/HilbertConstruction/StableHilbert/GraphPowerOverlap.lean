import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerChartMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelTransitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementRestriction

/-! # Graph Power Overlap -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerOverlap.StableHilbertGraphPowerOverlap

noncomputable section

/-! The original full-level family comparison transports graph-power
membership across stable Hilbert overlaps. This supplies the actual
overlap lifts for every presented graph-power locus. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (d : ℕ) (δ : Fin g → ℕ) (Φ : GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ)
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)

include hD in
theorem lifts_iff {T : Over (Spec (.of R))} [IsLocallyNoetherian T.left]
    (u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)
    (v : T ⟶ LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels)
    (h : (u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) ≫
        ChartPullbacks.stableHilbertChartToRank R i j D H =
      (v ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) ≫
        ChartPullbacks.stableHilbertChartToRank R i k D H) :
    (∃ z : T ⟶ GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ,
      z ≫ GraphPowerParameter.StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ = u) ↔
    (∃ z : T ⟶ GraphPowerParameter.StableHilbertGraphPower.parameter R i k D H hH g Hm Hi N labels d δ Φ,
      z ≫ GraphPowerParameter.StableHilbertGraphPower.inclusion R i k D H hH g Hm Hi N labels d δ Φ = v) := by
  rw [GraphPowerParameter.StableHilbertGraphPower.lifts_iff, GraphPowerParameter.StableHilbertGraphPower.lifts_iff]
  exact @GraphPower.EnhancementRestriction.graphPowerEnhancement_nonempty_iff_of_groupIso T.left g N δ
    (LevelComparison.StableHilbertLevelComparison.familyAt R i D H hH g Hm Hi N labels j u)
    (LevelComparison.StableHilbertLevelComparison.familyAt R i D H hH g Hm Hi N labels k v)
    (LevelComparison.StableHilbertLevelComparison.lineAt R i D H hH g Hm Hi N labels j u)
    (LevelComparison.StableHilbertLevelComparison.lineAt R i D H hH g Hm Hi N labels k v) d
    (LevelComparison.StableHilbertLevelComparison.familyIso R i D H hH hD g Hm Hi N labels j k u v h)
    (LevelComparison.StableHilbertLevelComparison.familyIso_isMonHom R i D H hH hD g Hm Hi N labels j k u v h)
    (LevelComparison.StableHilbertLevelComparison.familyIso_line R i D H hH hD g Hm Hi N labels j k u v h)

include hD in
theorem hasPoint_of_rank_eq {T : Over (Spec (.of R))} [IsLocallyNoetherian T.left]
    (a : T ⟶ GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ)
    (b : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D H)
    (h : (a ≫ GraphPowerChartMaps.StableHilbertGraphPower.toHilbertChart R i j D H hH g Hm Hi N labels d δ Φ) ≫
        ChartPullbacks.stableHilbertChartToRank R i j D H = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D H) :
    ∃ z : T ⟶ GraphPowerParameter.StableHilbertGraphPower.parameter R i k D H hH g Hm Hi N labels d δ Φ,
      z ≫ GraphPowerChartMaps.StableHilbertGraphPower.toHilbertChart R i k D H hH g Hm Hi N labels d δ Φ = b := by
  let u := a ≫ GraphPowerParameter.StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ
  have hu : u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels =
      a ≫ GraphPowerChartMaps.StableHilbertGraphPower.toHilbertChart R i j D H hH g Hm Hi N labels d δ Φ :=
    Category.assoc _ _ _
  have hsource : ∃! v : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels,
      v ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels =
        a ≫ GraphPowerChartMaps.StableHilbertGraphPower.toHilbertChart R i j D H hH g Hm Hi N labels d δ Φ :=
    ⟨u, hu, fun v hv => (cancel_mono
      (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)).mp (hv.trans hu.symm)⟩
  obtain ⟨v, hv, _⟩ := (LevelTransitions.stableHilbertFullLevel_noetherian_lift_iff
    R i D H hH hD g Hm Hi N labels j k
    (a ≫ GraphPowerChartMaps.StableHilbertGraphPower.toHilbertChart R i j D H hH g Hm Hi N labels d δ Φ) b h).mp hsource
  have huv : (u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) ≫
        ChartPullbacks.stableHilbertChartToRank R i j D H =
      (v ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) ≫
        ChartPullbacks.stableHilbertChartToRank R i k D H :=
    (congrArg (fun f => f ≫ ChartPullbacks.stableHilbertChartToRank R i j D H) hu).trans
      (h.trans (congrArg (fun f => f ≫ ChartPullbacks.stableHilbertChartToRank R i k D H) hv).symm)
  obtain ⟨z, hz⟩ := (lifts_iff R i D H hH hD g Hm Hi N labels d δ Φ j k u v huv).mp ⟨a, rfl⟩
  refine ⟨z, ?_⟩
  exact (Category.assoc z
    (GraphPowerParameter.StableHilbertGraphPower.inclusion R i k D H hH g Hm Hi N labels d δ Φ)
    (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)).symm.trans
      ((congrArg (fun f => f ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)
        hz).trans hv)

theorem exists_ambientLift :
    ∃ e : pullback
        (GraphPowerChartMaps.StableHilbertGraphPower.toHilbertChart R i j D H hH g Hm Hi N labels d δ Φ ≫
          Scheme.stableHilbertChartOver R i D H hH hD j)
        (Scheme.stableHilbertChartOver R i D H hH hD k) ⟶
      GraphPowerParameter.StableHilbertGraphPower.parameter R i k D H hH g Hm Hi N labels d δ Φ,
      e ≫ GraphPowerChartMaps.StableHilbertGraphPower.toHilbertChart R i k D H hH g Hm Hi N labels d δ Φ =
        pullback.snd
          (GraphPowerChartMaps.StableHilbertGraphPower.toHilbertChart R i j D H hH g Hm Hi N labels d δ Φ ≫
            Scheme.stableHilbertChartOver R i D H hH hD j)
          (Scheme.stableHilbertChartOver R i D H hH hD k) := by
  let p := GraphPowerChartMaps.StableHilbertGraphPower.toHilbertChart R i j D H hH g Hm Hi N labels d δ Φ
  let a := Scheme.stableHilbertChartOver R i D H hH hD j
  let b := Scheme.stableHilbertChartOver R i D H hH hD k
  let : IsOpenImmersion b.left := Scheme.stableHilbertChart_open R i D H hH hD k
  let : IsLocallyNoetherian (pullback (p ≫ a) b).left :=
    NoetherianCharts.overPullback_locallyNoetherian_of_open (p ≫ a) b
  apply hasPoint_of_rank_eq R i D H hH hD g Hm Hi N labels d δ Φ j k
    (pullback.fst (p ≫ a) b) (pullback.snd (p ≫ a) b)
  have h := congrArg (fun z => z ≫ Scheme.stableHilbertRankParameterOver R i D H hH hD)
    (pullback.condition (f := p ≫ a) (g := b))
  simpa only [p, a, b, Category.assoc, Scheme.stableHilbertChartOver_rankParameter] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerOverlap.StableHilbertGraphPowerOverlap
