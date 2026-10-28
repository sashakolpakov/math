import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.GraphPowerPresentationCompleteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerFrameCoverage

/-! # Graph Power Completeness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerCompleteness.StableHilbertGraphPower

noncomputable section

/-! Geometric completeness on the factory's stable graph-power charts.
Only the level, rather than every integer, must be invertible on the base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped BigOperators
variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (d : ℕ) (δ : Fin g → ℕ) (Φ : GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ)

local notation "M" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ
local notation "A" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.universalFamily R i j D H hH g Hm Hi N labels d δ Φ
local notation "P" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.universalPresentation R i j D H hH g Hm Hi N labels d δ Φ

theorem universalPresentation_geometricallyComplete
    (hd : 0 < d) (hNR : IsUnit (N : R)) (hg : 0 < g) (hN : 3 ≤ N)
    (hn : n + 1 = (2 : ℕ) ^ g * (∏ k, δ k) * d ^ g) :
    ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily (A).abelian.scheme.hom (P).ampleLineBundle.sheaf
      (P).canonicalSectionData.sections (𝟙 (M).left) := by
  have hunit : IsUnit (N : Γ((M).left, ⊤)) := by
    simpa only [map_natCast] using hNR.map (Coefficient.ModulePresheaf.schemeCoefficientMap (M).hom)
  exact Positive.GraphPowerPresentationCompleteness.StableHilbertCoverage.canonicalPositiveGraphPowerPresentation_geometricallyComplete
    (A) (P) d hd (fun k => labels (j.frame k))
    (GraphPowerFrameCoverage.StableHilbertGraphPower.universalPresentation_standardFrame R i j D H hH g Hm Hi N labels d δ Φ)
    (GraphPowerFrameCoverage.StableHilbertGraphPower.universalPresentation_normalizedPowerClass R i j D H hH g Hm Hi N labels d δ Φ)
    hg hN hunit hn

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerCompleteness.StableHilbertGraphPower
