import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelMonomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.QuasiProjectivity

/-! # Polarization Chart Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationChartMaps.StableHilbertPolarization

noncomputable section

/-! The actual normalized polarization chart maps monomorphically and
with finite type to its original stable Hilbert chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)

def toHilbertChart : PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ ⟶
    Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H :=
  PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ ≫
    LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels

instance toHilbertChart_mono :
    Mono (toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) := by
  dsimp only [toHilbertChart]
  infer_instance

instance toHilbertChart_left_mono :
    Mono (toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ).left :=
  Over.mono_left_of_mono _

instance parameter_noetherian :
    IsNoetherian (PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ).left :=
  (PolarizationParameter.StableHilbertPolarization.quasiProjective R i j D H hH g Hm Hi N labels qR d hd δ hδ).noetherian

instance toHilbertChart_locallyOfFiniteType :
    LocallyOfFiniteType (toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ).left := by
  dsimp only [toHilbertChart, Over.comp_left]
  infer_instance

instance toHilbertChart_quasiCompact :
    QuasiCompact (toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ).left := inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationChartMaps.StableHilbertPolarization
