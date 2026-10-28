import OAI.Analysis.PDE.Concentration.RadialBarrier

namespace OAI.Analysis.PDE.Concentration

open Set
open scoped ContDiff

/-- The inner-to-outer logarithmic barrier, with a quadratic correction
that absorbs the finite-time Dirichlet eigenvalue. -/
noncomputable def cylinderEscapeBarrier (ρ r : ℝ) : ℝ :=
  Real.log r - Real.log ρ + (-Real.log ρ) * (r ^ 2 - ρ ^ 2)

noncomputable def cylinderEscapeBarrierDeriv (ρ r : ℝ) : ℝ :=
  1 / r + 2 * (-Real.log ρ) * r

theorem contDiffOn_cylinderEscapeBarrier (ρ : ℝ) :
    ContDiffOn ℝ ∞ (cylinderEscapeBarrier ρ) (Ioi 0) := by
  have hl : ContDiffOn ℝ ∞ Real.log (Ioi 0) :=
    fun r hr => (Real.contDiffAt_log.mpr hr.ne').contDiffWithinAt
  exact (hl.sub contDiffOn_const).add
    (contDiffOn_const.mul ((contDiffOn_id.pow 2).sub contDiffOn_const))

theorem hasDerivAt_cylinderEscapeBarrier (ρ : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (cylinderEscapeBarrier ρ) (cylinderEscapeBarrierDeriv ρ r) r := by
  convert ((Real.hasDerivAt_log hr.ne').sub_const (Real.log ρ)).add
    ((((hasDerivAt_id r).pow 2).sub_const (ρ ^ 2)).const_mul (-Real.log ρ)) using 1
  · rfl
  · dsimp [cylinderEscapeBarrierDeriv]
    ring

theorem hasDerivAt_cylinderEscapeBarrierDeriv (ρ : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (cylinderEscapeBarrierDeriv ρ) (-1 / r ^ 2 + 2 * (-Real.log ρ)) r := by
  convert ((hasDerivAt_id r).inv hr.ne').add
    ((hasDerivAt_id r).const_mul (2 * (-Real.log ρ))) using 1
  · funext x
    simp [cylinderEscapeBarrierDeriv, one_div]
  · simp

theorem cylinderEscapeBarrier_radial_laplacian (ρ : ℝ) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (cylinderEscapeBarrier ρ)) r + deriv (cylinderEscapeBarrier ρ) r / r =
      4 * (-Real.log ρ) := by
  have he : deriv (cylinderEscapeBarrier ρ) =ᶠ[nhds r] cylinderEscapeBarrierDeriv ρ := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with x hx
    exact (hasDerivAt_cylinderEscapeBarrier ρ hx).deriv
  rw [he.deriv_eq, (hasDerivAt_cylinderEscapeBarrierDeriv ρ hr).deriv,
    (hasDerivAt_cylinderEscapeBarrier ρ hr).deriv]
  dsimp [cylinderEscapeBarrierDeriv]
  field_simp
  ring

@[simp] theorem cylinderEscapeBarrier_inner (ρ : ℝ) : cylinderEscapeBarrier ρ ρ = 0 := by
  simp [cylinderEscapeBarrier]

theorem cylinderEscapeBarrier_bounds {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (hr1 : r ≤ 1) :
    0 ≤ cylinderEscapeBarrier ρ r ∧ cylinderEscapeBarrier ρ r ≤ 2 * (-Real.log ρ) := by
  have hr := hρ.trans_le hρr
  have hρ1 := hρr.trans hr1
  have hL : 0 ≤ -Real.log ρ := neg_nonneg.mpr (Real.log_nonpos hρ.le hρ1)
  have hloglo := Real.log_le_log hρ hρr
  have hloghi := Real.log_nonpos hr.le hr1
  have hsq : 0 ≤ r ^ 2 - ρ ^ 2 := by nlinarith
  have hsq1 : r ^ 2 - ρ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ρ]
  have hlo := mul_nonneg hL hsq
  have hhi := mul_le_mul_of_nonneg_left hsq1 hL
  dsimp [cylinderEscapeBarrier]
  constructor <;> nlinarith

theorem cylinderEscapeBarrier_subsolution {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (hr1 : r ≤ 1) :
    cylinderEscapeBarrier ρ r / 100 ≤
      deriv (deriv (cylinderEscapeBarrier ρ)) r + deriv (cylinderEscapeBarrier ρ) r / r := by
  rw [cylinderEscapeBarrier_radial_laplacian ρ (hρ.trans_le hρr)]
  have hb := (cylinderEscapeBarrier_bounds hρ hρr hr1).2
  have hL : 0 ≤ -Real.log ρ := neg_nonneg.mpr (Real.log_nonpos hρ.le (hρr.trans hr1))
  linarith

theorem cylinderEscapeBarrier_outer_pos {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    0 < cylinderEscapeBarrier ρ 1 := by
  have hL : 0 < -Real.log ρ := neg_pos.mpr (Real.log_neg hρ hρ1)
  have hsq : 0 ≤ 1 - ρ ^ 2 := by nlinarith
  simp only [cylinderEscapeBarrier, Real.log_one, zero_sub, one_pow]
  exact add_pos_of_pos_of_nonneg hL (mul_nonneg hL.le hsq)

theorem cylinderEscapeBarrier_double_lower {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    Real.log 2 ≤ cylinderEscapeBarrier ρ (2 * ρ) := by
  have hL : 0 ≤ -Real.log ρ := neg_nonneg.mpr (Real.log_nonpos hρ.le hρ1.le)
  have hsq : 0 ≤ (2 * ρ) ^ 2 - ρ ^ 2 := by nlinarith [sq_nonneg ρ]
  rw [cylinderEscapeBarrier, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hρ.ne']
  nlinarith [mul_nonneg hL hsq]

theorem cylinderEscapeBarrier_ratio_lower {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    Real.log 2 / (2 * (-Real.log ρ)) ≤ cylinderEscapeBarrier ρ (2 * ρ) / cylinderEscapeBarrier ρ 1 := by
  exact div_le_div₀ ((Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans
    (cylinderEscapeBarrier_double_lower hρ hρ1)) (cylinderEscapeBarrier_double_lower hρ hρ1)
    (cylinderEscapeBarrier_outer_pos hρ hρ1) (cylinderEscapeBarrier_bounds hρ hρ1.le le_rfl).2

end OAI.Analysis.PDE.Concentration
