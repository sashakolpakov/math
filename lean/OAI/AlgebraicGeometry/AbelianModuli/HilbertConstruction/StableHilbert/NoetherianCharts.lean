import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankChartPullbacks
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.ConfigurationLocus

/-! # Noetherian Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NoetherianCharts

noncomputable section

/-! The stable rank and Hilbert charts over a Noetherian
coefficient ring are locally Noetherian schemes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ} (i : Fin m)

instance stableBalancedQuotientScheme_isNoetherian :
    IsNoetherian (Stable.BalancedProjectiveOpen.stableBalancedQuotientScheme R (r := n + 1) i).left := by
  obtain ⟨Q⟩ := Stable.BalancedProjectiveOpen.stableBalancedQuotientScheme_quasiProjective R i (Nat.succ_pos n)
  exact Q.noetherian

instance stableConfigurationPolynomialRankLocus_locallyNoetherian
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (D q : ℕ) :
    IsLocallyNoetherian (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D q).left :=
  LocallyOfFiniteType.isLocallyNoetherian (Stable.RankChartsOverBase.stableRankChartToStable R i j D q).left

instance stableConfigurationHilbertLocus_locallyNoetherian
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (D : ℕ) (P : Polynomial ℚ) :
    IsLocallyNoetherian (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P).left :=
  LocallyOfFiniteType.isLocallyNoetherian (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P).left

instance stableConfigurationHilbertRankInclusion_mono
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (D : ℕ) (P : Polynomial ℚ) :
    Mono (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P) := Over.mono_of_mono_left _

theorem overPullback_locallyNoetherian_of_open {S : Scheme.{u}} {M X N : Over S}
    (f : X ⟶ M) (a : N ⟶ M) [IsLocallyNoetherian X.left] [IsOpenImmersion a.left] :
    IsLocallyNoetherian (pullback f a).left := by
  have : IsOpenImmersion (pullback.fst f a).left := MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    ((IsPullback.of_hasPullback f a).map (Over.forget S)).flip
      (inferInstanceAs (IsOpenImmersion a.left))
  exact isLocallyNoetherian_of_isOpenImmersion (pullback.fst f a).left

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NoetherianCharts
