import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankAmbientPullback

/-! # Rank Scheme Immersion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankSchemeImmersion

noncomputable section

/-! The global polynomial rank locus is a quasi-compact immersion
into the stable configuration open. Both properties are checked
on its actual ambient affine chart pullbacks. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {n m : ℕ} (i : Fin m) (D q : ℕ)

instance stablePolynomialRankParameter_isImmersion :
    IsImmersion (PolynomialRankScheme.stablePolynomialRankParameter R (n := n) i D q) := by
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsImmersion)
    (BalancedAffineCover.stableBalancedAffineOpenCover R (r := n + 1) i)).mpr
  intro j
  change BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m at j
  let hp := RankAmbientPullback.stablePolynomialRankChart_isPullback R i D q j
  have he := hp.isoPullback_inv_snd
  have hi : IsImmersion (hp.isoPullback.inv ≫
      (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D q).left) := inferInstance
  rw [he] at hi
  exact hi

instance stablePolynomialRankParameter_quasiCompact :
    QuasiCompact (PolynomialRankScheme.stablePolynomialRankParameter R (n := n) i D q) := by
  have : IsZariskiLocalAtTarget @QuasiCompact.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @QuasiCompact)
    (BalancedAffineCover.stableBalancedAffineOpenCover R (r := n + 1) i)).mpr
  intro j
  change BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m at j
  let hp := RankAmbientPullback.stablePolynomialRankChart_isPullback R i D q j
  have he := hp.isoPullback_inv_snd
  have hi : QuasiCompact (hp.isoPullback.inv ≫
      (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D q).left) := inferInstance
  rw [he] at hi
  exact hi

instance stablePolynomialRankParameterOver_isImmersion :
    IsImmersion (PolynomialRankScheme.stablePolynomialRankParameterOver R (n := n) i D q).left :=
  stablePolynomialRankParameter_isImmersion R i D q

instance stablePolynomialRankParameterOver_quasiCompact :
    QuasiCompact (PolynomialRankScheme.stablePolynomialRankParameterOver R (n := n) i D q).left :=
  stablePolynomialRankParameter_quasiCompact R i D q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankSchemeImmersion
