import OAI.Analysis.Calculus.Current.ComplexDerivatives

namespace OAI.Analysis.Calculus.Current

noncomputable section

def tangentSlope {d : ℕ} (v : Fin d → ℝ) (z h : Index d → ℂ) : Index d → ℂ
  | none => 0
  | some none => -(∑ i, ratioSlope z h i * (v i : ℂ)) / 2
  | some (some i) => ratioSlope z h i / 2

theorem hasDerivAt_tangentField_line {d : ℕ} (v : Fin d → ℝ)
    (z h : Index d → ℂ) (hY : z none ≠ 0) (b : Index d) :
    HasDerivAt (fun t : ℝ => tangentField v (imaginaryLine z h t) b)
      (tangentSlope v z h b) 0 := by
  cases b with
  | none => exact hasDerivAt_const _ _
  | some b =>
    cases b with
    | none =>
      simpa only [tangentField, tangentVector, tangentSlope, Pi.neg_apply,
        Finset.sum_apply] using ((HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
        (hasDerivAt_ratio_line z h hY i).mul_const (v i : ℂ))).neg).div_const 2
    | some i =>
      exact ((hasDerivAt_ratio_line z h hY i).const_add (v i : ℂ)).div_const 2

theorem tangentSlope_I {d : ℕ} (v : Fin d → ℝ)
    (z h : Index d → ℂ) (b : Index d) :
    tangentSlope v z (fun a => Complex.I * h a) b =
      Complex.I * tangentSlope v z h b := by
  cases b with
  | none => simp [tangentSlope]
  | some b =>
    cases b with
    | none => simp only [tangentSlope, ratioSlope_I, mul_assoc, ← Finset.mul_sum]; ring
    | some i => simp only [tangentSlope, ratioSlope_I]; ring

theorem complexBarDirectional_conjugate_tangentField {d : ℕ} (v : Fin d → ℝ)
    (z h : Index d → ℂ) (hY : z none ≠ 0) (b : Index d) :
    complexBarDirectional (fun w => star (tangentField v w b)) z h =
      2 * star (tangentSlope v z h b) := by
  unfold complexBarDirectional
  rw [(hasDerivAt_tangentField_line v z h hY b).star.deriv,
    (hasDerivAt_tangentField_line v z (fun a => Complex.I * h a) hY b).star.deriv,
    tangentSlope_I]
  simp only [star_mul, Complex.star_def, Complex.conj_I]
  ring_nf
  simp
  ring

def movingUnit {d : ℕ} (z : Index d → ℂ) : ℂ := z none / (‖z none‖ : ℂ)

theorem differentiableAt_movingUnit {d : ℕ} (z : Index d → ℂ) (hY : z none ≠ 0) :
    DifferentiableAt ℝ (movingUnit (d := d)) z := by
  have hn : (‖z none‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hY
  have hy : DifferentiableAt ℝ (fun w : Index d → ℂ => (‖w none‖ : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z
      ((differentiableAt_apply none z).norm ℂ hY)
  unfold movingUnit
  simpa only [div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply] using
    (differentiableAt_apply (𝕜 := ℝ) none z).fun_mul (hy.inv hn)

theorem hasDerivAt_conjugate_movingUnit_line {d : ℕ} (z h : Index d → ℂ)
    (hY : z none ≠ 0) :
    HasDerivAt (fun t : ℝ => star (movingUnit (imaginaryLine z h t)))
      ((star (h none) * (‖z none‖ : ℂ) - star (z none) * (radiusSlope z h : ℂ)) /
        (‖z none‖ : ℂ) ^ 2) 0 := by
  have hn : (‖z none‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hY
  have hh := ((hasDerivAt_imaginaryLine z h none).star).div
    (hasDerivAt_radius_line z h hY).ofReal_comp (by simpa using hn)
  convert hh using 1
  · funext t
    simp [movingUnit, star_div₀]
  · simp

theorem complexBarDirectional_conjugate_movingUnit {d : ℕ} (z h : Index d → ℂ)
    (hY : z none ≠ 0) :
    complexBarDirectional (fun w => star (movingUnit w)) z h =
      star (h none) / (‖z none‖ : ℂ) := by
  unfold complexBarDirectional
  rw [(hasDerivAt_conjugate_movingUnit_line z h hY).deriv,
    (hasDerivAt_conjugate_movingUnit_line z (fun a => Complex.I * h a) hY).deriv]
  have hn : (‖z none‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hY
  have hp := radiusSlope_pair z h
  have hs := norm_square_eq_mul_star (z none)
  simp only [star_mul, Complex.star_def, Complex.conj_I]
  calc
    _ = 2 * star (h none) / (‖z none‖ : ℂ) -
        star (z none) / (‖z none‖ : ℂ) ^ 2 *
          ((radiusSlope z h : ℂ) + Complex.I *
            (radiusSlope z (fun a => Complex.I * h a) : ℂ)) := by
      simp only [Complex.star_def]
      field_simp
      ring_nf
      simp
      ring
    _ = _ := by
      rw [hp]
      simp only [Complex.star_def] at hs ⊢
      field_simp
      linear_combination (starRingEnd ℂ (h none)) * hs

theorem movingUnit_mul_star {d : ℕ} (z : Index d → ℂ) (hY : z none ≠ 0) :
    movingUnit z * star (movingUnit z) = 1 := by
  have hn : (‖z none‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hY
  have hs := norm_square_eq_mul_star (z none)
  simp only [movingUnit, star_div₀, Complex.star_def, Complex.conj_ofReal]
  field_simp
  exact hs.symm

end
end OAI.Analysis.Calculus.Current
