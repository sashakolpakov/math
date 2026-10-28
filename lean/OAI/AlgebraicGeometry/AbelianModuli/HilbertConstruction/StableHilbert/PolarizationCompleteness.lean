import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPresentationCompleteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationFrameCoverage

/-! # Polarization Completeness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationCompleteness.StableHilbertPolarization

noncomputable section

/-! The actual marked frame and graph-power section rank give geometric
completeness of the canonical sections on each uniform stable chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)

local notation "M" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ
local notation "A" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.universalFamily R i j D H hH g Hm Hi N labels qR d hd δ hδ
local notation "P" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.universalPresentation R i j D H hH g Hm Hi N labels qR d hd δ hδ

theorem universalPresentation_geometricallyComplete
    (hg : 0 < g) (hN : 3 ≤ N)
    (hd_eq : d = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (hn : n + 1 = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ) :
    ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily (A).abelian.scheme.hom (P).ampleLineBundle.sheaf
      (P).canonicalSectionData.sections (𝟙 (M).left) := by
  have hunit : IsUnit (N : Γ((M).left, ⊤)) := by
    have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hNq).map
      (Coefficient.ModulePresheaf.schemeCoefficientMap ((M).hom ≫ qR))
  have hpow := PolarizationFrameCoverage.StableHilbertPolarization.universalPresentation_normalizedPowerClass R i j D H hH g Hm Hi N labels qR d hd δ hδ
  have hpow' : Line.Bundles.LineBundle.classOf ((A).abelian.zeroNormalizedBundle (P).ampleLineBundle) =
      Line.Bundles.LineBundle.classOf ((A).graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)) :=
    hpow.trans (congrArg (fun k => Line.Bundles.LineBundle.classOf ((A).graphBundle.tensorPower k)) hd_eq)
  exact GraphPresentationCompleteness.StableHilbertCoverage.canonicalGraphPresentation_geometricallyComplete (A) (P)
    (fun k => labels (j.frame k))
    (PolarizationFrameCoverage.StableHilbertPolarization.universalPresentation_standardFrame R i j D H hH g Hm Hi N labels qR d hd δ hδ)
    hpow' hg hδ hN hunit hn

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationCompleteness.StableHilbertPolarization
