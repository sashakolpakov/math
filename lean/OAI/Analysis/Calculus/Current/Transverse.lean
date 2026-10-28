import OAI.Analysis.Calculus.Current.Fiber.TimeBounds

/-! The pushforward of the radial field in the defining holomorphic coordinates. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open OAI.Analysis.Calculus.Quaternion
open scoped Matrix Matrix.Norms.Elementwise

def radialHeight {d : ℕ} (z : Index d → ℂ) : ℂ :=
  (phi z - z none * fiberQuadratic (ratio z)) / fiberDenominator (ratio z)

def fiberRadialField {d : ℕ} (z : Index d → ℂ) : Index d → ℂ
  | none => radialHeight z
  | some none => radialHeight z
  | some (some i) => ratio z i * (z none + radialHeight z)

theorem fiberRadialField_time_zero {d : ℕ} (z : Index d → ℂ) :
    fiberRadialField z none - fiberRadialField z (some none) = 0 := sub_self _

theorem ratioRow_fiberRadialField {d : ℕ} (z : Index d → ℂ)
    (hY : z none ≠ 0) (i : Fin d) :
    ∑ b, ratioRow z i b * fiberRadialField z b = ratio z i := by
  simp [ratioRow, fiberRadialField, Fintype.sum_option]
  field_simp
  ring

theorem phaseRow_fiberRadialField {d : ℕ} (z : Index d → ℂ)
    (hD : fiberDenominator (ratio z) ≠ 0) :
    ∑ b, phaseRow (ratio z) b * fiberRadialField z b = phi z := by
  simp only [Fintype.sum_option, phaseRow, fiberRadialField, one_mul]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  change -(fiberQuadratic (ratio z)) / 2 * radialHeight z +
    (radialHeight z + fiberQuadratic (ratio z) * (z none + radialHeight z)) = _
  unfold radialHeight
  have he : fiberDenominator (ratio z) = 1 + fiberQuadratic (ratio z) / 2 := rfl
  rw [he] at hD ⊢
  have h₂ : 2 + fiberQuadratic (ratio z) ≠ 0 := by
    intro h
    apply hD
    linear_combination h / 2
  field_simp [h₂]
  ring

theorem fiberJacobian_fiberRadialField {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (hD : fiberDenominator (ratio z) ≠ 0) :
    fiberJacobian w a z *ᵥ fiberRadialField z = fiberMap w a z := by
  funext i
  cases i with
  | none =>
    simp only [Matrix.mulVec, dotProduct, fiberJacobian, mul_assoc, ← Finset.mul_sum,
      phaseRow_fiberRadialField z hD, fiberMap]
    ring
  | some i =>
    simp only [Matrix.mulVec, dotProduct, fiberJacobian, mul_assoc, ← Finset.mul_sum,
      ratioRow_fiberRadialField z hY i, fiberMap]
    ring

theorem fderiv_fiberDefining_radial {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (hD : fiberDenominator (ratio z) ≠ 0) :
    fderiv ℝ (fiberDefining w a) z (fiberRadialField z) = 2 * (fiberDefining w a z + 1) := by
  have hf (i : Option (Fin d)) :=
    (contDiffAt_fiberMap_complex w a z hY i).differentiableAt (by norm_num)
  have hd (i : Option (Fin d)) :
      fderiv ℝ (fun q => ‖fiberMap w a q i‖ ^ 2) z (fiberRadialField z) =
        2 * ‖fiberMap w a z i‖ ^ 2 := by
    rw [(hf i |>.hasFDerivAt.restrictScalars ℝ).norm_sq.fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, two_smul]
    change inner ℝ (fiberMap w a z i)
      (fderiv ℂ (fun q => fiberMap w a q i) z (fiberRadialField z)) +
      inner ℝ (fiberMap w a z i)
      (fderiv ℂ (fun q => fiberMap w a q i) z (fiberRadialField z)) = _
    rw [fderiv_fiberMap w a z _ hY i, congrFun (fiberJacobian_fiberRadialField w a z hY hD) i]
    simp [] ; ring
  unfold fiberDefining
  rw [fderiv_sub_const, fderiv_fun_sum]
  · simp only [sum_apply, hd, ← Finset.mul_sum]
    ring
  · intro i _
    exact ((hf i).restrictScalars ℝ).norm_sq ℂ

/-- A uniformly positive transverse coefficient, without dividing by a gradient. -/
theorem radial_transverse_coefficient {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (hr : fiberDefining (1 / 10) a z ≤ 0) :
    1 ≤ fderiv ℝ (fiberDefining (1 / 10) a) z (fiberRadialField z) +
      (fiberDefining (1 / 10) a z) ^ 2 := by
  rw [fderiv_fiberDefining_radial _ _ _ hY (fiberDenominator_ne_zero_on_fiber a z hr)]
  nlinarith [sq_nonneg (fiberDefining (1 / 10) a z + 1)]

theorem contDiffAt_radialHeight {d : ℕ} (z : Index d → ℂ)
    (hY : z none ≠ 0) (hD : fiberDenominator (ratio z) ≠ 0) :
    ContDiffAt ℝ ⊤ (radialHeight : (Index d → ℂ) → ℂ) z := by
  have hQ : ContDiffAt ℝ ⊤ (fun q => fiberQuadratic (ratio q)) z := by
    apply ContDiffAt.sum
    intro i _
    exact (contDiffAt_ratio z hY i).mul (contDiffAt_ratio z hY i)
  have hYf : ContDiffAt ℝ ⊤ (fun q : Index d → ℂ => q none) z := by fun_prop
  have hDf : ContDiffAt ℝ ⊤ (fun q => fiberDenominator (ratio q)) z := by
    exact contDiffAt_const.add (hQ.div_const 2)
  have hN : ContDiffAt ℝ ⊤ (fun q => phi q - q none * fiberQuadratic (ratio q)) z :=
    (contDiffAt_phi_real z hY).sub (hYf.mul hQ)
  simpa only [radialHeight, div_eq_mul_inv, Pi.inv_apply] using! hN.mul (hDf.inv hD)

theorem contDiffAt_fiberRadialField {d : ℕ} (z : Index d → ℂ)
    (hY : z none ≠ 0) (hD : fiberDenominator (ratio z) ≠ 0) :
    ContDiffAt ℝ ⊤ (fiberRadialField : (Index d → ℂ) → Index d → ℂ) z := by
  apply contDiffAt_pi.mpr
  intro i
  cases i with
  | none => exact contDiffAt_radialHeight z hY hD
  | some i =>
    cases i with
    | none => exact contDiffAt_radialHeight z hY hD
    | some i =>
      have hYf : ContDiffAt ℝ ⊤ (fun q : Index d → ℂ => q none) z := by fun_prop
      exact (contDiffAt_ratio z hY i).mul (hYf.add (contDiffAt_radialHeight z hY hD))

theorem radialHeight_norm_le {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (ha : 0 < a) (hay : a ≤ ‖z none‖) (hr : fiberDefining (1 / 10) a z ≤ 0) :
    ‖radialHeight z‖ ≤ ‖z none‖ := by
  have hQ := (norm_fiberQuadratic_le (ratio z)).trans (fiber_ratio_bound (1 / 10) a z (by norm_num) hr)
  have hP := fiber_phase_norm_le a ha z hr
  have hD := fiberDenominator_norm_lower a z hr
  have hDpos : 0 < ‖fiberDenominator (ratio z)‖ := by linarith
  unfold radialHeight
  rw [norm_div, div_le_iff₀ hDpos]
  calc
    ‖phi z - z none * fiberQuadratic (ratio z)‖ ≤
        ‖phi z‖ + ‖z none‖ * ‖fiberQuadratic (ratio z)‖ := by
      simpa only [norm_mul] using norm_sub_le (phi z) (z none * fiberQuadratic (ratio z))
    _ ≤ a / 10 + ‖z none‖ * (1 / 10 : ℝ) ^ 2 :=
      add_le_add hP (mul_le_mul_of_nonneg_left hQ (norm_nonneg _))
    _ ≤ ‖z none‖ * ‖fiberDenominator (ratio z)‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hD (norm_nonneg (z none))]

theorem fiberRadialField_norm_le {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (ha : 0 < a) (hay : a ≤ ‖z none‖) (hr : fiberDefining (1 / 10) a z ≤ 0) :
    ‖fiberRadialField z‖ ≤ 2 * ‖z none‖ := by
  have hH := radialHeight_norm_le a z ha hay hr
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * ‖z none‖)).mpr
  intro i
  cases i with
  | none => exact hH.trans (by nlinarith [norm_nonneg (z none)])
  | some i =>
    cases i with
    | none => exact hH.trans (by nlinarith [norm_nonneg (z none)])
    | some i =>
      change ‖ratio z i * (z none + radialHeight z)‖ ≤ _
      rw [norm_mul]
      calc
        _ ≤ 1 * (‖z none‖ + ‖radialHeight z‖) :=
          mul_le_mul (fiber_ratio_coordinate_le_one a z hr i) (norm_add_le _ _)
            (norm_nonneg _) (by norm_num)
        _ ≤ _ := by linarith

theorem fiberRadialField_norm_le_on_time_strip {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (ha : 0 < a) (hr : fiberDefining (1 / 10) a z ≤ 0)
    (ht : a ≤ ‖imaginaryTime z‖) (ht' : ‖imaginaryTime z‖ ≤ 4) :
    ‖fiberRadialField z‖ ≤ 24 := by
  have hb := fiberRadialField_norm_le a z ha (fiber_height_ge_scale a ha z hr ht) hr
  have hy := fiber_height_le_time a ha z hr ht
  linarith

end OAI.Analysis.Calculus.Current
