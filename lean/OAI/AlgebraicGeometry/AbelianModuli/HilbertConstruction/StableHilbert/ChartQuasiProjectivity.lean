import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NoetherianCharts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveImmersions

/-! # Chart Quasi Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ChartQuasiProjectivity

noncomputable section

/-! Each actual stable Hilbert chart has a quasi-projective presentation
over the coefficient ring, obtained from its immersion into the stable
configuration scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (D : ℕ) (P : Polynomial ℚ)

instance stableConfigurationPolynomialRankLocus_noetherian (q : ℕ) :
    IsNoetherian (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D q).left := by
  have : CompactSpace (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j).left :=
    inferInstanceAs (CompactSpace (Spec (.of
      (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced))))
  let : CompactSpace (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D q).left :=
    QuasiCompact.compactSpace_of_compactSpace
      (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D q).left
  exact ⟨⟩

instance stableConfigurationHilbertLocus_noetherian :
    IsNoetherian (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P).left := by
  let : CompactSpace (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P).left :=
    QuasiCompact.compactSpace_of_compactSpace (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P).left
  exact ⟨⟩

def stableConfigurationHilbertChartQuasiProjective :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P) := by
  let Q := Classical.choice (Stable.BalancedProjectiveOpen.stableBalancedQuotientScheme_quasiProjective R i (Nat.succ_pos n))
  let a := Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P ≫
    Stable.RankChartsOverBase.stableRankChartToStable R i j D (Stable.ConfigurationLocus.configurationHilbertRank D P)
  letI : IsImmersion a.left := by
    change IsImmersion ((Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P).left ≫
      (Stable.RankChartsOverBase.stableRankChartToStable R i j D (Stable.ConfigurationLocus.configurationHilbertRank D P)).left)
    infer_instance
  letI : QuasiCompact (a ≫ Q.embedding).left := inferInstance
  letI : IsImmersion (a ≫ Q.embedding).left :=
    inferInstanceAs (IsImmersion (a.left ≫ Q.embedding.left))
  exact Q.projective.quasiProjectiveImmersion (a ≫ Q.embedding)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ChartQuasiProjectivity
