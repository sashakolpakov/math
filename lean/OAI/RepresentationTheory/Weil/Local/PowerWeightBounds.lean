import OAI.RepresentationTheory.Weil.Local.RealPower

/-! # Power Weight Bounds -/

namespace OAI.RepresentationTheory.Weil.Local.PowerWeightBounds.Construction

noncomputable section

section

/-! Second derivatives and the radial Laplacian of the power-damped inverse-radius weight. -/

def realPowerWeightSecondDerivative (s ε t : ℝ) : ℝ :=
  Real.exp (-ε * t ^ s) * ((ε * s * t ^ s) ^ 2 + ε * s * (3 - s) * t ^ s + 2) / t ^ 3

theorem realPowerWeightDerivative_hasDerivAt (s ε t : ℝ) (ht : 0 < t) :
    HasDerivAt (RealPower.Construction.realPowerWeightDerivative s ε) (realPowerWeightSecondDerivative s ε t) t := by
  have hp := Real.hasDerivAt_rpow_const (p := s) (Or.inl ht.ne')
  have hd := ((((hp.const_mul (-ε)).exp).neg).mul
    ((hp.const_mul (ε * s)).add_const 1)).div ((hasDerivAt_id t).pow 2) (pow_ne_zero _ ht.ne')
  dsimp only [id_eq, Pi.pow_apply, Pi.neg_apply, Pi.mul_apply] at hd
  convert! hd using 1
  unfold realPowerWeightSecondDerivative
  rw [Real.rpow_sub_one ht.ne']
  field_simp
  ring

theorem realPowerWeight_radial_laplacian (s ε t : ℝ) (ht : t ≠ 0) :
    t * realPowerWeightSecondDerivative s ε t + RealPower.Construction.realPowerWeightDerivative s ε t =
      Real.exp (-ε * t ^ s) * ((ε * s * t ^ s) ^ 2 + ε * s * (2 - s) * t ^ s + 1) / t ^ 2 := by
  unfold realPowerWeightSecondDerivative RealPower.Construction.realPowerWeightDerivative
  field_simp
  ring

theorem exp_neg_linear_bound (u : ℝ) :
    Real.exp (-u) * (u + 1) ≤ 1 := by
  rw [Real.exp_neg, inv_mul_eq_div]
  exact (div_le_one (Real.exp_pos u)).mpr (Real.add_one_le_exp u)

theorem exp_neg_quadratic_bound (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-u) * (u ^ 2 + 2 * u + 2) ≤ 2 := by
  rw [Real.exp_neg, inv_mul_eq_div]
  apply (div_le_iff₀ (Real.exp_pos u)).mpr
  nlinarith [Real.quadratic_le_exp_of_nonneg hu]

end

/-! Uniform inverse-power bounds for the radial damping weight and its derivatives. -/

theorem realPowerWeightDerivative_abs_le (s ε t : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1) (hε : 0 ≤ ε) (ht : 0 < t) :
    |RealPower.Construction.realPowerWeightDerivative s ε t| ≤ 1 / t ^ 2 := by
  let u := ε * t ^ s
  have hu : 0 ≤ u := mul_nonneg hε (Real.rpow_nonneg ht.le s)
  have heq : |RealPower.Construction.realPowerWeightDerivative s ε t| = Real.exp (-u) * (s * u + 1) / t ^ 2 := by
    rw [RealPower.Construction.realPowerWeightDerivative, abs_div, abs_mul, abs_neg,
      abs_of_pos (Real.exp_pos _), abs_of_nonneg (by positivity : 0 ≤ ε * s * t ^ s + 1),
      abs_of_nonneg (sq_nonneg t)]
    dsimp [u]
    congr 1
    ring_nf
  rw [heq]
  apply div_le_div_of_nonneg_right _ (sq_nonneg t)
  calc
    _ ≤ Real.exp (-u) * (u + 1) := mul_le_mul_of_nonneg_left
      (by nlinarith [mul_le_mul_of_nonneg_right hs1 hu]) (Real.exp_pos _).le
    _ ≤ 1 := exp_neg_linear_bound u

theorem realPowerWeightSecondDerivative_nonneg (s ε t : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1) (hε : 0 ≤ ε) (ht : 0 < t) :
    0 ≤ realPowerWeightSecondDerivative s ε t := by
  have h3 : 0 ≤ 3 - s := by linarith
  unfold realPowerWeightSecondDerivative
  positivity

theorem realPowerWeightSecondDerivative_le (s ε t : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1) (hε : 0 ≤ ε) (ht : 0 < t) :
    realPowerWeightSecondDerivative s ε t ≤ 2 / t ^ 3 := by
  let u := ε * t ^ s
  have hu : 0 ≤ u := mul_nonneg hε (Real.rpow_nonneg ht.le s)
  have heq : realPowerWeightSecondDerivative s ε t =
      Real.exp (-u) * ((s * u) ^ 2 + s * (3 - s) * u + 2) / t ^ 3 := by
    unfold realPowerWeightSecondDerivative
    dsimp [u]
    congr 1
    ring_nf
  rw [heq]
  apply div_le_div_of_nonneg_right _ (pow_nonneg ht.le 3)
  have hsu : s * u ≤ u := by nlinarith [mul_le_mul_of_nonneg_right hs1 hu]
  have hsq : (s * u) ^ 2 ≤ u ^ 2 := (sq_le_sq₀ (mul_nonneg hs.le hu) hu).mpr hsu
  have hcoef : s * (3 - s) ≤ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (by linarith : 0 ≤ 2 - s)]
  calc
    _ ≤ Real.exp (-u) * (u ^ 2 + 2 * u + 2) := mul_le_mul_of_nonneg_left
      (by nlinarith [mul_le_mul_of_nonneg_right hcoef hu]) (Real.exp_pos _).le
    _ ≤ 2 := exp_neg_quadratic_bound u hu

theorem realPowerWeight_radial_laplacian_nonneg (s ε t : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1) (hε : 0 ≤ ε) (ht : 0 < t) :
    0 ≤ t * realPowerWeightSecondDerivative s ε t + RealPower.Construction.realPowerWeightDerivative s ε t := by
  rw [realPowerWeight_radial_laplacian s ε t ht.ne']
  have h2 : 0 ≤ 2 - s := by linarith
  positivity

theorem realPowerWeight_radial_laplacian_le (s ε t : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1) (hε : 0 ≤ ε) (ht : 0 < t) :
    t * realPowerWeightSecondDerivative s ε t + RealPower.Construction.realPowerWeightDerivative s ε t ≤ 2 / t ^ 2 := by
  calc
    _ ≤ t * realPowerWeightSecondDerivative s ε t := by
      have h := RealPower.Construction.realPowerWeightDerivative_nonpos s ε t hs hε ht
      linarith
    _ ≤ t * (2 / t ^ 3) := mul_le_mul_of_nonneg_left
      (realPowerWeightSecondDerivative_le s ε t hs hs1 hε ht) ht.le
    _ = 2 / t ^ 2 := by field_simp

end

end OAI.RepresentationTheory.Weil.Local.PowerWeightBounds.Construction
