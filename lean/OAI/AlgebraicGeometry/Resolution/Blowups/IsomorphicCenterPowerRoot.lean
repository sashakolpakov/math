import OAI.AlgebraicGeometry.Resolution.Blowups.RegularRadicalPowerRoot
import OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicBlowupCenterReduced
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealChartDescent
import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedCoefficientIdeal

/-! # Isomorphic Center Power Root -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicCenterPowerRoot.Construction

noncomputable section

/-! Exact coefficient power bounds for smooth centers whose actual blowup is an isomorphism. -/

open _root_.CategoryTheory

universe u

variable (k : Type u) {R : Type u} [Field k] [IsAlgClosed k]
  [CommRing R] [Algebra k R] [IsNoetherianRing R]

/-- Power roots along a smooth center descend from its actual regular,
reduced principal exceptional ideals on the isomorphic blowup cover. -/
theorem smooth_isIso_center_ideal_power_root (I J : Ideal R)
    [Algebra.Smooth k (R ⧸ I)] [IsIso (ReesGrading.Construction.affineBlowupToSpec I)]
    (m q : ℕ) (hq : 0 < q) (hJ : J ^ q ≤ I ^ (m * q)) : J ≤ I ^ m := by
  apply Affine.IdealChartDescent.Construction.ideal_le_of_isIso_blowup_chart_maps I J (I ^ m)
  intro a
  have hmap : (J ^ q).map (Blowup.Charts.Construction.blowupChartConstants I a) ≤
      (I ^ (m * q)).map (Blowup.Charts.Construction.blowupChartConstants I a) := Ideal.map_mono hJ
  rw [Ideal.map_pow, Ideal.map_pow, ExceptionalIdeal.Construction.blowupChart_extendedIdeal] at hmap
  rw [Ideal.map_pow, ExceptionalIdeal.Construction.blowupChart_extendedIdeal]
  exact RegularRadicalPowerRoot.Construction.regular_radical_principal_ideal_power_root (Blowup.Charts.Construction.blowupChartConstants I a a.val)
    (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a) (IsomorphicBlowupCenterReduced.Construction.blowupChart_exceptional_span_isRadical k I a)
    (J.map (Blowup.Charts.Construction.blowupChartConstants I a)) m q hq hmap

/-- The weighted factorial control is exactly equivalent to all original
coefficient controls for every such smooth center, without a principal generator. -/
theorem smooth_isIso_center_weighted_iff (I : Ideal R)
    [Algebra.Smooth k (R ⧸ I)] [IsIso (ReesGrading.Construction.affineBlowupToSpec I)]
    (b : ℕ) (J : Fin b → Ideal R) :
    WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b J ≤ I ^ b.factorial ↔ ∀ j, J j ≤ I ^ (b - j.val) := by
  constructor
  · intro h j
    have hj := (le_iSup (fun i => J i ^ WeightedCoefficientIdeal.Construction.coefficientWeight b i) j).trans h
    rw [← WeightedCoefficientIdeal.Construction.coefficientWeight_mul_control b j] at hj
    exact smooth_isIso_center_ideal_power_root k I (J j) (b - j.val)
      (WeightedCoefficientIdeal.Construction.coefficientWeight b j) (WeightedCoefficientIdeal.Construction.coefficientWeight_pos b j) hj
  · exact WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_le_pow I b J

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicCenterPowerRoot.Construction
