import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Kernel

/-! Harmonicity and size estimates for the actual Newtonian kernel away from its pole. -/

noncomputable section
open scoped RealInnerProductSpace Topology
open InnerProductSpace Laplacian
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem radial_rpow_step (p : ℝ) {x : E} (hx : x ≠ 0) :
    (‖x‖ ^ 2) ^ (p - 2) * ‖x‖ ^ 2 = (‖x‖ ^ 2) ^ (p - 1) := by
  rw [← Real.rpow_add_one (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))]
  congr 1
  ring

theorem radialPowerHessian_apply_bound (p : ℝ) (x v w : E) :
    ‖radialPowerHessian p x v w‖ ≤ (|2 * p * (‖x‖ ^ 2) ^ (p - 1)| +
      |4 * p * (p - 1) * (‖x‖ ^ 2) ^ (p - 2)| * ‖x‖ ^ 2) * ‖v‖ * ‖w‖ := by
  let A := 2 * p * (‖x‖ ^ 2) ^ (p - 1)
  let B := 4 * p * (p - 1) * (‖x‖ ^ 2) ^ (p - 2)
  rw [radialPowerHessian_apply, Real.norm_eq_abs]
  change |A * ⟪v, w⟫ + B * ⟪x, v⟫ * ⟪x, w⟫| ≤ (|A| + |B| * ‖x‖ ^ 2) * ‖v‖ * ‖w‖
  calc
    _ ≤ |A * ⟪v, w⟫| + |B * ⟪x, v⟫ * ⟪x, w⟫| := abs_add_le _ _
    _ = |A| * |⟪v, w⟫| + |B| * |⟪x, v⟫| * |⟪x, w⟫| := by simp only [abs_mul]
    _ ≤ |A| * (‖v‖ * ‖w‖) + |B| * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖) := by
      gcongr <;> exact abs_real_inner_le_norm _ _
    _ = _ := by ring

theorem radialPowerHessian_norm_le_raw (p : ℝ) (x : E) :
    ‖radialPowerHessian p x‖ ≤ |2 * p * (‖x‖ ^ 2) ^ (p - 1)| +
      |4 * p * (p - 1) * (‖x‖ ^ 2) ^ (p - 2)| * ‖x‖ ^ 2 := by
  apply (radialPowerHessian p x).opNorm_le_bound (by positivity)
  intro v
  apply (radialPowerHessian p x v).opNorm_le_bound (by positivity)
  intro w
  exact radialPowerHessian_apply_bound p x v w

theorem radialPowerHessian_norm_le (p : ℝ) {x : E} (hx : x ≠ 0) :
    ‖radialPowerHessian p x‖ ≤
      (|2 * p| + |4 * p * (p - 1)|) * (‖x‖ ^ 2) ^ (p - 1) := by
  have h := radialPowerHessian_norm_le_raw p x
  rw [abs_mul (2 * p), abs_mul (4 * p * (p - 1)),
    abs_of_nonneg (Real.rpow_nonneg (sq_nonneg ‖x‖) (p - 1)),
    abs_of_nonneg (Real.rpow_nonneg (sq_nonneg ‖x‖) (p - 2)),
    mul_assoc _ ((‖x‖ ^ 2) ^ (p - 2)), radial_rpow_step p hx, ← add_mul] at h
  exact h

theorem laplacian_radialPower [FiniteDimensional ℝ E] (p : ℝ) {x : E} (hx : x ≠ 0) :
    (laplacian (radialPower p : E → ℝ) : E → ℝ) x =
      2 * p * ((Module.finrank ℝ E : ℝ) + 2 * (p - 1)) * (‖x‖ ^ 2) ^ (p - 1) := by
  let b := stdOrthonormalBasis ℝ E
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (radialPower p) b]
  have hterm (i : Fin (Module.finrank ℝ E)) :
      iteratedFDeriv ℝ 2 (radialPower p) x ![b i, b i] =
        2 * p * (‖x‖ ^ 2) ^ (p - 1) +
        (4 * p * (p - 1) * (‖x‖ ^ 2) ^ (p - 2)) * ⟪x, b i⟫ ^ 2 := by
    rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
    change (fderiv ℝ (fderiv ℝ (radialPower p)) x) (b i) (b i) = _
    rw [second_fderiv_radialPower p hx]
    rw [radialPowerHessian_apply, b.inner_eq_one]
    ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, b.sum_sq_inner_left]
  rw [mul_assoc _ ((‖x‖ ^ 2) ^ (p - 2)), radial_rpow_step p hx]
  ring

def newtonianKernel (m : ℕ) (x : E) : ℝ := radialPower (1 - (m : ℝ) / 2) x

omit [InnerProductSpace ℝ E] in
theorem newtonianKernel_eq_norm_rpow (m : ℕ) (x : E) :
    newtonianKernel m x = ‖x‖ ^ (2 - (m : ℝ)) := by
  unfold newtonianKernel radialPower
  rw [← Real.rpow_natCast_mul (norm_nonneg x)]
  congr 1
  push_cast
  ring

theorem laplacian_newtonianKernel [FiniteDimensional ℝ E] {x : E} (hx : x ≠ 0) :
    (laplacian (newtonianKernel (Module.finrank ℝ E) : E → ℝ) : E → ℝ) x = 0 := by
  change (laplacian (radialPower (1 - (Module.finrank ℝ E : ℝ) / 2) : E → ℝ) : E → ℝ) x = 0
  rw [laplacian_radialPower _ hx]
  have he : (Module.finrank ℝ E : ℝ) + 2 * (1 - (Module.finrank ℝ E : ℝ) / 2 - 1) = 0 := by ring
  rw [he, mul_zero, zero_mul]

theorem harmonicAt_newtonianKernel [FiniteDimensional ℝ E] {x : E} (hx : x ≠ 0) :
    HarmonicAt (newtonianKernel (Module.finrank ℝ E)) x := by
  refine ⟨(contDiffAt_radialPower _ hx).of_le (by norm_num), ?_⟩
  filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
  exact laplacian_newtonianKernel hy

theorem newtonianKernel_second_fderiv_norm_le (m : ℕ) {x : E} (hx : x ≠ 0) :
    ‖fderiv ℝ (fderiv ℝ (newtonianKernel m)) x‖ ≤
      (|2 - (m : ℝ)| + |(m : ℝ) * ((m : ℝ) - 2)|) * ‖x‖ ^ (-(m : ℝ)) := by
  change ‖fderiv ℝ (fderiv ℝ (radialPower (1 - (m : ℝ) / 2))) x‖ ≤ _
  rw [second_fderiv_radialPower _ hx]
  have hc1 : 2 * (1 - (m : ℝ) / 2) = 2 - (m : ℝ) := by ring
  have hc2 : 4 * (1 - (m : ℝ) / 2) * (1 - (m : ℝ) / 2 - 1) =
      (m : ℝ) * ((m : ℝ) - 2) := by ring
  have hp : (‖x‖ ^ 2) ^ (1 - (m : ℝ) / 2 - 1) = ‖x‖ ^ (-(m : ℝ)) := by
    rw [← Real.rpow_natCast_mul (norm_nonneg x)]
    congr 1
    push_cast
    ring
  simpa only [hc1, hc2, hp] using radialPowerHessian_norm_le (1 - (m : ℝ) / 2) hx

end OAI.Analysis.PDE.Schauder
