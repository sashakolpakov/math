import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelMonomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.QuasiProjectivity

/-! # Graph Power Chart Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerChartMaps.StableHilbertGraphPower

noncomputable section

/-! The graph-power locus chart retains its original finite-type
monomorphism to the stable Hilbert chart over the arithmetic base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (d : ℕ) (δ : Fin g → ℕ) (Φ : GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ)

def toHilbertChart : GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ ⟶
    Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H :=
  GraphPowerParameter.StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ ≫
    LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels

instance toHilbertChart_mono :
    Mono (toHilbertChart R i j D H hH g Hm Hi N labels d δ Φ) := by
  dsimp only [toHilbertChart]
  infer_instance

instance toHilbertChart_left_mono :
    Mono (toHilbertChart R i j D H hH g Hm Hi N labels d δ Φ).left :=
  Over.mono_left_of_mono _

instance toHilbertChart_locallyOfFiniteType :
    LocallyOfFiniteType (toHilbertChart R i j D H hH g Hm Hi N labels d δ Φ).left := by
  dsimp only [toHilbertChart, Over.comp_left]
  infer_instance

instance toHilbertChart_quasiCompact :
    QuasiCompact (toHilbertChart R i j D H hH g Hm Hi N labels d δ Φ).left := by
  dsimp only [toHilbertChart, Over.comp_left]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerChartMaps.StableHilbertGraphPower
