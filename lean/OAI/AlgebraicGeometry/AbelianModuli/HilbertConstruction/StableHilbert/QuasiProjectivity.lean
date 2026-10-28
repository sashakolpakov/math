import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AmbientPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankQuasiProjectivity

/-! # Quasi Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.QuasiProjectivity

noncomputable section

/-! The glued Hilbert condition is a closed subscheme of the
quasi-projective global rank scheme over a Noetherian ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)

instance stableHilbertRankParameter_closed : IsClosedImmersion (Scheme.stableHilbertRankParameter R i D P hP hD) := by
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    (Stable.PolynomialRankScheme.stablePolynomialRankGlueData R (n := n) i D (Stable.ConfigurationLocus.configurationHilbertRank D P)).openCover).mpr
  intro j
  change ULift.{u} (Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) at j
  have : IsClosedImmersion (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j.down D P).left :=
    Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion_isClosedImmersion R i j.down D P hP ((le_max_right _ _).trans hD)
  let hp := AmbientPullback.stableHilbertChart_isPullback R i D P hP hD j.down
  have he := hp.isoPullback_inv_snd
  have hi : IsClosedImmersion (hp.isoPullback.inv ≫ (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j.down D P).left) :=
    inferInstance
  rw [he] at hi
  exact hi

instance stableHilbertRankParameterOver_closed :
    IsClosedImmersion (Scheme.stableHilbertRankParameterOver R i D P hP hD).left :=
  stableHilbertRankParameter_closed R i D P hP hD

theorem stableHilbertOver_quasiProjective :
    Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation (Scheme.stableHilbertOver R i D P hP hD)) := by
  obtain ⟨Q⟩ := Stable.RankQuasiProjectivity.stablePolynomialRankOver_quasiProjective R (n := n) i D (Stable.ConfigurationLocus.configurationHilbertRank D P)
  exact ⟨Q.ofClosedImmersion (Scheme.stableHilbertRankParameterOver R i D P hP hD)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.QuasiProjectivity
