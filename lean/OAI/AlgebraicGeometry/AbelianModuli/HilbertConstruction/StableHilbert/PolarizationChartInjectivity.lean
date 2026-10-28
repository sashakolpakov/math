import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationCoordinateOrbits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LiftRecovery

/-! # Polarization Chart Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationChartInjectivity.StableHilbertPolarizationGluing

noncomputable section

/-! Original polarized full-level isomorphisms determine the images
of affine chart points in the actual glued stable parameter. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)

local notation "G" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ
local notation "M[" j "]" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ
local notation "F[" j "]" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.universalFamily R i j D H hH g Hm Hi N labels qR d hd δ hδ
local notation "u[" j "]" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationGluing.StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j
local notation "c[" j "]" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationMarkedPoints.StableHilbertPolarization.toCoefficientChart R i j D H hH g Hm Hi N labels qR d hd δ hδ
local notation "q" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationGluing.StableHilbertPolarizationGluing.toBalanced R i D H hH hD g Hm Hi N labels qR d hd δ hδ

theorem chartMap_toBalanced (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    u[j] ≫ q = c[j] ≫ Stable.RankChartsOverBase.stableBalancedAffineChartOverMap R i j := by
  change u[j] ≫ (PolarizationGluing.StableHilbertPolarizationGluing.inclusion R i D H hH hD g Hm Hi N labels qR d hd δ hδ ≫
    LiftRecovery.stableHilbertParameterToStable R i D H hH hD) = _
  rw [← Category.assoc, PolarizationGluing.StableHilbertPolarizationGluing.chartMap_inclusion, Category.assoc, LiftRecovery.stableHilbertChartOver_toStable]
  simp only [PolarizationChartMaps.StableHilbertPolarization.toHilbertChart,
    LevelMonomorphism.StableHilbertLevel.toHilbertChart,
    PolarizationMarkedPoints.StableHilbertPolarization.toCoefficientChart,
    PolarizationMarkedPoints.StableHilbertFullLevel.parameterToCoefficientChart,
    LevelParameter.StableHilbertLevel.toCoefficientChart, Category.assoc]

/-- Equality of chart images follows from an original moduli
isomorphism; no relation between their embeddings is an input. -/
theorem affineChartPoints_eq_of_iso
    (hg : 0 < g) (hN : 3 ≤ N)
    (hd_eq : d = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (hn : n + 1 = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ)
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)
    {T : Over (Spec (.of R))} [IsAffine T.left] [IsLocallyNoetherian T.left]
    (a : T ⟶ M[j]) (b : T ⟶ M[k])
    (e : Moduli.Isomorphisms.LevelPreservingIso ((F[j]).pullback a.left) ((F[k]).pullback b.left)) :
    a ≫ u[j] = b ≫ u[k] := by
  apply (cancel_mono q).mp
  have he := PolarizationCoordinateOrbits.StableHilbertPolarization.affinePoints_toBalanced_eq_of_iso
    R i D H hH g Hm Hi N labels qR d hd δ hδ hg hN hd_eq hn j k a b e
  simpa only [Category.assoc, chartMap_toBalanced] using he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationChartInjectivity.StableHilbertPolarizationGluing
