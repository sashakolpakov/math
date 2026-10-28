import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Regularized

/-! Uniform singular majorants for the smooth Newtonian regularizations. -/

noncomputable section
open scoped RealInnerProductSpace Topology
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem shiftedRadialHessian_apply_bound (p s : ℝ) (x v w : E) :
    ‖shiftedRadialHessian p s x v w‖ ≤ (|2 * p * (s + ‖x‖ ^ 2) ^ (p - 1)| +
      |4 * p * (p - 1) * (s + ‖x‖ ^ 2) ^ (p - 2)| * ‖x‖ ^ 2) * ‖v‖ * ‖w‖ := by
  rw [shiftedRadialHessian_apply, Real.norm_eq_abs]
  calc
    _ ≤ |2 * p * (s + ‖x‖ ^ 2) ^ (p - 1) * ⟪v, w⟫| +
        |4 * p * (p - 1) * (s + ‖x‖ ^ 2) ^ (p - 2) * ⟪x, v⟫ * ⟪x, w⟫| := abs_add_le _ _
    _ = |2 * p * (s + ‖x‖ ^ 2) ^ (p - 1)| * |⟪v, w⟫| +
        |4 * p * (p - 1) * (s + ‖x‖ ^ 2) ^ (p - 2)| * |⟪x, v⟫| * |⟪x, w⟫| := by
      simp only [abs_mul]
    _ ≤ |2 * p * (s + ‖x‖ ^ 2) ^ (p - 1)| * (‖v‖ * ‖w‖) +
        |4 * p * (p - 1) * (s + ‖x‖ ^ 2) ^ (p - 2)| * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖) := by
      gcongr <;> exact abs_real_inner_le_norm _ _
    _ = _ := by ring

theorem shiftedRadialHessian_apply_le_singular {p s : ℝ} (hp : p ≤ 1) (hs : 0 ≤ s)
    {x : E} (hx : x ≠ 0) (v w : E) :
    ‖shiftedRadialHessian p s x v w‖ ≤
      (|2 * p| + |4 * p * (p - 1)|) * (‖x‖ ^ 2) ^ (p - 1) * ‖v‖ * ‖w‖ := by
  have hx2 : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hsx : 0 < s + ‖x‖ ^ 2 := add_pos_of_nonneg_of_pos hs hx2
  have hrad : (s + ‖x‖ ^ 2) ^ (p - 2) * ‖x‖ ^ 2 ≤ (s + ‖x‖ ^ 2) ^ (p - 1) := by
    calc
      _ ≤ (s + ‖x‖ ^ 2) ^ (p - 2) * (s + ‖x‖ ^ 2) := by gcongr; linarith
      _ = _ := by rw [← Real.rpow_add_one hsx.ne']; congr 1; ring
  have hpow : (s + ‖x‖ ^ 2) ^ (p - 1) ≤ (‖x‖ ^ 2) ^ (p - 1) :=
    Real.rpow_le_rpow_of_nonpos hx2 (by linarith) (by linarith)
  have hc : |2 * p * (s + ‖x‖ ^ 2) ^ (p - 1)| +
      |4 * p * (p - 1) * (s + ‖x‖ ^ 2) ^ (p - 2)| * ‖x‖ ^ 2 ≤
        (|2 * p| + |4 * p * (p - 1)|) * (‖x‖ ^ 2) ^ (p - 1) := by
    rw [abs_mul (2 * p), abs_mul (4 * p * (p - 1)),
      abs_of_nonneg (Real.rpow_nonneg hsx.le _), abs_of_nonneg (Real.rpow_nonneg hsx.le _)]
    have h1 := mul_le_mul_of_nonneg_left hrad (abs_nonneg (4 * p * (p - 1)))
    have h2 := mul_le_mul_of_nonneg_left hpow (add_nonneg (abs_nonneg (2 * p)) (abs_nonneg (4 * p * (p - 1))))
    nlinarith
  exact (shiftedRadialHessian_apply_bound p s x v w).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (norm_nonneg v)) (norm_nonneg w))

theorem shiftedNewtonianHessian_bound (m : ℕ) {s : ℝ} (hs : 0 ≤ s)
    {x : E} (hx : x ≠ 0) (v w : E) :
    ‖shiftedRadialHessian (1 - (m : ℝ) / 2) s x v w‖ ≤
      newtonianSizeConstant m * ‖x‖ ^ (-(m : ℝ)) * ‖v‖ * ‖w‖ := by
  have h := shiftedRadialHessian_apply_le_singular (p := 1 - (m : ℝ) / 2)
    (by linarith [Nat.cast_nonneg (α := ℝ) m]) hs hx v w
  have hc1 : 2 * (1 - (m : ℝ) / 2) = 2 - (m : ℝ) := by ring
  have hc2 : 4 * (1 - (m : ℝ) / 2) * (1 - (m : ℝ) / 2 - 1) = (m : ℝ) * (m - 2) := by ring
  have hp : (‖x‖ ^ 2) ^ (1 - (m : ℝ) / 2 - 1) = ‖x‖ ^ (-(m : ℝ)) := by
    rw [← Real.rpow_natCast_mul (norm_nonneg x)]
    congr 1
    norm_num
    ring
  simpa only [hc1, hc2, hp, newtonianSizeConstant] using h

theorem tendsto_shiftedRadialHessian (p : ℝ) {x : E} (hx : x ≠ 0) (v w : E) :
    Filter.Tendsto (fun s : ℝ => shiftedRadialHessian p s x v w) (𝓝 0)
      (𝓝 (radialPowerHessian p x v w)) := by
  have hbase : ContinuousAt (fun s : ℝ => s + ‖x‖ ^ 2) 0 := by fun_prop
  have hne : (0 : ℝ) + ‖x‖ ^ 2 ≠ 0 := by simpa using pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have h1 := hbase.rpow_const (p := p - 1) (Or.inl hne)
  have h2 := hbase.rpow_const (p := p - 2) (Or.inl hne)
  have ht : ContinuousAt (fun s : ℝ =>
      2 * p * (s + ‖x‖ ^ 2) ^ (p - 1) * ⟪v, w⟫ +
      4 * p * (p - 1) * (s + ‖x‖ ^ 2) ^ (p - 2) * ⟪x, v⟫ * ⟪x, w⟫) 0 :=
    ((continuousAt_const.mul h1).mul continuousAt_const).add
      (((continuousAt_const.mul h2).mul continuousAt_const).mul continuousAt_const)
  simpa only [shiftedRadialHessian_apply, radialPowerHessian_apply, zero_add] using ht.tendsto

end OAI.Analysis.PDE.Schauder
