import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerCoordinateOrbits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LiftRecovery

/-! # Graph Power Chart Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerChartInjectivity.StableHilbertGraphPowerGluing

noncomputable section

/-! Original polarized full-level isomorphisms determine the images
of affine chart points in the actual glued stable parameter. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped BigOperators

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (d : ℕ) (δ : Fin g → ℕ) (Φ : GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ)

local notation "G" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerGluing.StableHilbertGraphPowerGluing.parameter R i D H hH hD g Hm Hi N labels d δ Φ
local notation "M[" j "]" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ
local notation "F[" j "]" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.universalFamily R i j D H hH g Hm Hi N labels d δ Φ
local notation "u[" j "]" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerGluing.StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ j
local notation "c[" j "]" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerMarkedPoints.StableHilbertGraphPower.toCoefficientChart R i j D H hH g Hm Hi N labels d δ Φ
local notation "q" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerGluing.StableHilbertGraphPowerGluing.toBalanced R i D H hH hD g Hm Hi N labels d δ Φ

theorem chartMap_toBalanced (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    u[j] ≫ q = c[j] ≫ Stable.RankChartsOverBase.stableBalancedAffineChartOverMap R i j := by
  change u[j] ≫ (GraphPowerGluing.StableHilbertGraphPowerGluing.inclusion R i D H hH hD g Hm Hi N labels d δ Φ ≫
    LiftRecovery.stableHilbertParameterToStable R i D H hH hD) = _
  rw [← Category.assoc, GraphPowerGluing.StableHilbertGraphPowerGluing.chartMap_inclusion, Category.assoc, LiftRecovery.stableHilbertChartOver_toStable]
  simp only [GraphPowerChartMaps.StableHilbertGraphPower.toHilbertChart,
    LevelMonomorphism.StableHilbertLevel.toHilbertChart,
    GraphPowerMarkedPoints.StableHilbertGraphPower.toCoefficientChart,
    PolarizationMarkedPoints.StableHilbertFullLevel.parameterToCoefficientChart,
    LevelParameter.StableHilbertLevel.toCoefficientChart, Category.assoc]

/-- Equality of chart images follows from an original moduli
isomorphism; no relation between their embeddings is an input. -/
theorem affineChartPoints_eq_of_iso
    (hd : 0 < d) (hNR : IsUnit (N : R))
    (hg : 0 < g) (hN : 3 ≤ N)
    (hn : n + 1 = (2 : ℕ) ^ g * (∏ k, δ k) * d ^ g)
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)
    {T : Over (Spec (.of R))} [IsAffine T.left] [IsLocallyNoetherian T.left]
    (a : T ⟶ M[j]) (b : T ⟶ M[k])
    (e : Moduli.Isomorphisms.LevelPreservingIso ((F[j]).pullback a.left) ((F[k]).pullback b.left)) :
    a ≫ u[j] = b ≫ u[k] := by
  apply (cancel_mono q).mp
  have he := GraphPowerCoordinateOrbits.StableHilbertGraphPower.affinePoints_toBalanced_eq_of_iso
    R i D H hH g Hm Hi N labels d δ Φ hd hNR hg hN hn j k a b e
  simpa only [Category.assoc, chartMap_toBalanced] using he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerChartInjectivity.StableHilbertGraphPowerGluing
