import OAI.Analysis.PDE.Concentration.Annulus

namespace OAI.Analysis.PDE.Concentration

open Set

/-- A logarithmic barrier whose positive radial Laplacian absorbs the
zeroth-order term produced by averaging over a fixed real-time interval. -/
noncomputable def cylinderRadialBarrier (r : ℝ) : ℝ :=
  (1 + r ^ 2 / 100) * (Real.log 3 - Real.log r) + (r ^ 2 - 9) / 100

noncomputable def cylinderRadialBarrierDeriv (r : ℝ) : ℝ :=
  r / 50 * (Real.log 3 - Real.log r) + r / 100 - 1 / r

theorem contDiffOn_cylinderRadialBarrier :
    ContDiffOn ℝ 2 cylinderRadialBarrier (Ioi 0) := by
  have hl : ContDiffOn ℝ 2 Real.log (Ioi 0) :=
    fun r hr => (Real.contDiffAt_log.mpr hr.ne').contDiffWithinAt
  exact ((contDiffOn_const.add ((contDiffOn_id.pow 2).div_const 100)).mul
    (contDiffOn_const.sub hl)).add (((contDiffOn_id.pow 2).sub contDiffOn_const).div_const 100)

theorem hasDerivAt_cylinderRadialBarrier {r : ℝ} (hr : 0 < r) :
    HasDerivAt cylinderRadialBarrier (cylinderRadialBarrierDeriv r) r := by
  have hlog := (Real.hasDerivAt_log hr.ne').const_sub (Real.log 3)
  have hsq := (hasDerivAt_id r).pow 2
  have h := (((hsq.div_const 100).const_add 1).mul hlog).add
    ((hsq.sub_const 9).div_const 100)
  convert h using 1
  · funext x
    simp [cylinderRadialBarrier]
  · dsimp [cylinderRadialBarrierDeriv]
    field_simp
    ring

theorem hasDerivAt_cylinderRadialBarrierDeriv {r : ℝ} (hr : 0 < r) :
    HasDerivAt cylinderRadialBarrierDeriv
      ((Real.log 3 - Real.log r) / 50 - 1 / 100 + 1 / r ^ 2) r := by
  have hlog := (Real.hasDerivAt_log hr.ne').const_sub (Real.log 3)
  have h := ((((hasDerivAt_id r).div_const 50).mul hlog).add
    ((hasDerivAt_id r).div_const 100)).sub ((hasDerivAt_id r).inv hr.ne')
  convert h using 1
  · funext x
    simp [cylinderRadialBarrierDeriv, one_div]
  · dsimp only [id_eq]
    field_simp
    ring

theorem cylinderRadialBarrier_radial_laplacian {r : ℝ} (hr : 0 < r) :
    deriv (deriv cylinderRadialBarrier) r + deriv cylinderRadialBarrier r / r =
      (Real.log 3 - Real.log r) / 25 := by
  have he : deriv cylinderRadialBarrier =ᶠ[nhds r] cylinderRadialBarrierDeriv := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with x hx
    exact (hasDerivAt_cylinderRadialBarrier hx).deriv
  rw [he.deriv_eq, (hasDerivAt_cylinderRadialBarrierDeriv hr).deriv,
    (hasDerivAt_cylinderRadialBarrier hr).deriv]
  dsimp [cylinderRadialBarrierDeriv]
  field_simp
  ring

@[simp] theorem cylinderRadialBarrier_three : cylinderRadialBarrier 3 = 0 := by
  norm_num [cylinderRadialBarrier]

theorem cylinderRadialBarrier_bounds {r : ℝ} (hr : 0 < r) (hr3 : r ≤ 3) :
    (Real.log 3 - Real.log r) / 2 ≤ cylinderRadialBarrier r ∧
      cylinderRadialBarrier r ≤ 2 * (Real.log 3 - Real.log r) := by
  let t := Real.log 3 - Real.log r
  have ht : 0 ≤ t := sub_nonneg.mpr (Real.log_le_log hr hr3)
  have hl : Real.log (r / 3) ≤ r / 3 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hr.ne' (by norm_num : (3 : ℝ) ≠ 0)] at hl
  have hquad : 9 - r ^ 2 ≤ 18 * t := by
    dsimp [t]
    nlinarith [sq_nonneg (r - 3)]
  have hr2 : r ^ 2 ≤ 9 := by nlinarith
  have hmul : r ^ 2 * t ≤ 9 * t := mul_le_mul_of_nonneg_right hr2 ht
  have hnonneg : 0 ≤ r ^ 2 * t := mul_nonneg (sq_nonneg r) ht
  change t / 2 ≤ (1 + r ^ 2 / 100) * t + (r ^ 2 - 9) / 100 ∧
    (1 + r ^ 2 / 100) * t + (r ^ 2 - 9) / 100 ≤ 2 * t
  constructor <;> nlinarith

theorem cylinderRadialBarrier_pos {r : ℝ} (hr : 0 < r) (hr3 : r < 3) :
    0 < cylinderRadialBarrier r := by
  have hl : 0 < Real.log 3 - Real.log r := sub_pos.mpr (Real.log_lt_log hr hr3)
  exact (half_pos hl).trans_le (cylinderRadialBarrier_bounds hr hr3.le).1

theorem cylinderRadialBarrier_subsolution {r : ℝ} (hr : 0 < r) (hr3 : r ≤ 3) :
    cylinderRadialBarrier r / 100 ≤
      deriv (deriv cylinderRadialBarrier) r + deriv cylinderRadialBarrier r / r := by
  rw [cylinderRadialBarrier_radial_laplacian hr]
  have hb := (cylinderRadialBarrier_bounds hr hr3).2
  have hl := sub_nonneg.mpr (Real.log_le_log hr hr3)
  linarith

end OAI.Analysis.PDE.Concentration
