import OAI.Analysis.Calculus.Current.Strong

/-! The holomorphic coordinates and defining function of the periodic fibers.
The fixed-time coordinate here is `T = Y - S₁ = √2 τ`, so that no choice of
square-root normalization enters the inversion argument. -/

namespace OAI.Analysis.Calculus.Current

noncomputable section

def fiberQuadratic {d : ℕ} (W : Fin d → ℂ) : ℂ := ∑ i, W i * W i

def fiberDenominator {d : ℕ} (W : Fin d → ℂ) : ℂ := 1 + fiberQuadratic W / 2

def fiberInverse {d : ℕ} (T : ℂ) (W : Fin d → ℂ) (F : ℂ) : Index d → ℂ
  | none => (T + F) / fiberDenominator W
  | some none => (T + F) / fiberDenominator W - T
  | some (some i) => W i * ((T + F) / fiberDenominator W)

theorem norm_fiberQuadratic_le {d : ℕ} (W : Fin d → ℂ) :
    ‖fiberQuadratic W‖ ≤ ∑ i, ‖W i‖ ^ 2 := by
  calc
    ‖fiberQuadratic W‖ ≤ ∑ i, ‖W i * W i‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, pow_two]

theorem fiberDenominator_ne_zero {d : ℕ} (W : Fin d → ℂ)
    (hW : (∑ i, ‖W i‖ ^ 2) < 2) : fiberDenominator W ≠ 0 := by
  have hb := norm_fiberQuadratic_le W
  have hsmall : ‖fiberQuadratic W / 2‖ < 1 := by
    rw [norm_div]
    norm_num
    linarith
  intro h
  have heq : fiberQuadratic W / 2 = -1 := by
    have := h
    unfold fiberDenominator at this
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using this)
  rw [heq] at hsmall
  norm_num at hsmall

theorem fiberInverse_Y_ne_zero {d : ℕ} (T F : ℂ) (W : Fin d → ℂ)
    (hN : T + F ≠ 0) (hD : fiberDenominator W ≠ 0) :
    fiberInverse T W F none ≠ 0 := div_ne_zero hN hD

theorem ratio_fiberInverse {d : ℕ} (T F : ℂ) (W : Fin d → ℂ)
    (hN : T + F ≠ 0) (hD : fiberDenominator W ≠ 0) :
    ratio (fiberInverse T W F) = W := by
  funext i
  simp [ratio, fiberInverse, div_ne_zero hN hD]

theorem fiberInverse_time {d : ℕ} (T F : ℂ) (W : Fin d → ℂ) :
    fiberInverse T W F none - fiberInverse T W F (some none) = T := by
  simp [fiberInverse]

private theorem fiberInverse_phi_algebra (T F q : ℂ)
    (_ : T + F ≠ 0) (hD : 1 + q / 2 ≠ 0) :
    (T + F) / (1 + q / 2) - T +
      q * ((T + F) / (1 + q / 2)) ^ 2 / (2 * ((T + F) / (1 + q / 2))) = F := by
  have h2 : 2 + q ≠ 0 := by
    intro h
    apply hD
    linear_combination h / 2
  field_simp [h2]
  ring

theorem phi_fiberInverse {d : ℕ} (T F : ℂ) (W : Fin d → ℂ)
    (hN : T + F ≠ 0) (hD : fiberDenominator W ≠ 0) :
    phi (fiberInverse T W F) = F := by
  have hs (Y : ℂ) : (∑ i, (W i * Y) * (W i * Y)) = fiberQuadratic W * Y ^ 2 := by
    simp only [fiberQuadratic, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [phi, fiberInverse]
  rw [hs]
  exact fiberInverse_phi_algebra T F (fiberQuadratic W) hN hD

/-- The holomorphic map whose squared norm defines the fiber. -/
def fiberMap {d : ℕ} (w a : ℝ) (z : Index d → ℂ) : Option (Fin d) → ℂ
  | none => 10 * phi z / (a : ℂ)
  | some i => ratio z i / (w : ℂ)

def fiberDefining {d : ℕ} (w a : ℝ) (z : Index d → ℂ) : ℝ :=
  (∑ i, ‖fiberMap w a z i‖ ^ 2) - 1

theorem fiberDefining_formula {d : ℕ} (w a : ℝ) (z : Index d → ℂ) :
    fiberDefining w a z =
      (∑ i, ‖ratio z i‖ ^ 2) / w ^ 2 + 100 * ‖phi z‖ ^ 2 / a ^ 2 - 1 := by
  simp only [fiberDefining, Fintype.sum_option, fiberMap, norm_div, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, div_pow, mul_pow, sq_abs]
  norm_num
  rw [← Finset.sum_div]
  ring

theorem contDiffAt_phi_real {d : ℕ} (z : Index d → ℂ) (hY : z none ≠ 0) :
    ContDiffAt ℝ ⊤ (phi : (Index d → ℂ) → ℂ) z := by
  unfold phi
  simp only [div_eq_mul_inv]
  fun_prop (disch := exact mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) hY)

theorem contDiffAt_fiberMap {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (i : Option (Fin d)) :
    ContDiffAt ℝ ⊤ (fun q => fiberMap w a q i) z := by
  cases i with
  | none => exact (contDiffAt_const.mul (contDiffAt_phi_real z hY)).div_const _
  | some i => exact (contDiffAt_ratio z hY i).div_const _

theorem contDiffAt_fiberDefining {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) : ContDiffAt ℝ ⊤ (fiberDefining w a) z := by
  apply ContDiffAt.sub _ contDiffAt_const
  apply ContDiffAt.sum
  intro i _
  exact (contDiffAt_fiberMap w a z hY i).norm_sq ℂ

theorem fiber_ratio_bound {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hw : 0 < w) (hr : fiberDefining w a z ≤ 0) :
    (∑ i, ‖ratio z i‖ ^ 2) ≤ w ^ 2 := by
  rw [fiberDefining_formula] at hr
  have hp : 0 ≤ 100 * ‖phi z‖ ^ 2 / a ^ 2 := by positivity
  have hb : (∑ i, ‖ratio z i‖ ^ 2) / w ^ 2 ≤ 1 := by linarith
  exact (div_le_one (sq_pos_of_pos hw)).mp hb

theorem fiberDenominator_ne_zero_on_fiber {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (hr : fiberDefining (1 / 10) a z ≤ 0) : fiberDenominator (ratio z) ≠ 0 := by
  apply fiberDenominator_ne_zero
  have hb := fiber_ratio_bound (1 / 10) a z (by norm_num) hr
  linarith

end
end OAI.Analysis.Calculus.Current
