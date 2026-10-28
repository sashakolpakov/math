import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ClosedPointPowerRoot
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.CenterPermissibility

/-! # Frame Center Power Root -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.FrameCenterPowerRoot.Construction

noncomputable section

/-! Exact coefficient powers along reduced dual-coordinate centers in arbitrary dimension. -/

variable (k : Type*) {R ι : Type*} [Field k] [IsAlgClosed k] [CommRing R]
  [Algebra k R] [Algebra.Smooth k R] [Algebra ℚ R] [Fintype ι] [DecidableEq ι]

include k in
/-- A reduced center with dual coordinate derivations has exact power
scaling, in any ambient dimension and without global étale coordinates. -/
theorem smooth_frame_center_ideal_power_root (z : ι → R) (D : ι → Derivation ℤ R R)
    (hD : ∀ i j, D i (z j) = if i = j then 1 else 0)
    (hI : (Ideal.span (Set.range z)).IsRadical) (J : Ideal R) (b e : ℕ) (he : 0 < e)
    (hJ : J ^ e ≤ (Ideal.span (Set.range z)) ^ (b * e)) :
    J ≤ (Ideal.span (Set.range z)) ^ b := by
  let : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
  cases b with
  | zero => simp only [pow_zero, Ideal.one_eq_top, le_top]
  | succ b =>
      apply (Coordinate.CenterPermissibility.Construction.coordinateCenter_permissible_iff_closedPoint_order z D hD hI J b).mpr
      intro q _ hq
      apply (ClosedWeightedOrder.Construction.closedPoint_local_order_iff J q (b + 1)).mpr
      exact ClosedPointPowerRoot.Construction.smooth_closedPoint_ideal_power_root k J q (b + 1) e he
        (hJ.trans (pow_le_pow_left' hq ((b + 1) * e)))

include k in
/-- The single factorial coefficient bound is equivalent to its full
family of component bounds along every reduced dual-coordinate center. -/
theorem smooth_frame_center_weighted_iff (z : ι → R) (D : ι → Derivation ℤ R R)
    (hD : ∀ i j, D i (z j) = if i = j then 1 else 0)
    (hI : (Ideal.span (Set.range z)).IsRadical) (b : ℕ) (J : Fin b → Ideal R) :
    WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b J ≤ (Ideal.span (Set.range z)) ^ b.factorial ↔
      ∀ j, J j ≤ (Ideal.span (Set.range z)) ^ (b - j.val) := by
  constructor
  · intro h j
    have hj := (le_iSup (fun i => J i ^ WeightedCoefficientIdeal.Construction.coefficientWeight b i) j).trans h
    rw [← WeightedCoefficientIdeal.Construction.coefficientWeight_mul_control b j] at hj
    exact smooth_frame_center_ideal_power_root k z D hD hI (J j) (b - j.val)
      (WeightedCoefficientIdeal.Construction.coefficientWeight b j) (WeightedCoefficientIdeal.Construction.coefficientWeight_pos b j) hj
  · exact WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_le_pow _ b J

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.FrameCenterPowerRoot.Construction
