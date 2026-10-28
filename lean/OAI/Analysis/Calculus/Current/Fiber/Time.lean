import OAI.Analysis.Calculus.Current.Fiber.Cofactor

/-! Strict positivity in the manuscript's physical-time direction. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open OAI.Analysis.Calculus.Quaternion
open scoped Matrix Matrix.Norms.Elementwise

private theorem complexK_apply_explicit (c : ℂ) :
    complexK c = (⟨c.re, 0, 0, c.im⟩ : Quaternion ℝ) := rfl

theorem fiberCofactor_column {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hw : w ≠ 0) (ha : a ≠ 0) (hY : z none ≠ 0) (i j : Index d) :
    fiberCofactor w a z i j =
      complexK (fiberKernelVector z i) * fiberCofactor w a z none j := by
  have h := fiberHessian_kernel_unique w a z _ hw ha hY
    (fiberCofactor_image_in_kernel w a z hY (Pi.single j 1))
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun h i

theorem fiberCofactor_entry {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hw : w ≠ 0) (ha : a ≠ 0) (hY : z none ≠ 0) (i j : Index d) :
    fiberCofactor w a z i j = complexK (fiberKernelVector z i) *
      fiberCofactor w a z none none * star (complexK (fiberKernelVector z j)) := by
  rw [fiberCofactor_column w a z hw ha hY i j,
    ← (fiberCofactor_isHermitian w a z).apply none j,
    fiberCofactor_column w a z hw ha hY j none, star_mul,
    (fiberCofactor_isHermitian w a z).apply none none, mul_assoc]

theorem fiberCofactor_rankOne {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hw : w ≠ 0) (ha : a ≠ 0) (hY : z none ≠ 0) :
    fiberCofactor w a z = (fiberCofactor w a z none none).re •
      OAI.Analysis.Calculus.Quaternion.outer (fun i => complexK (fiberKernelVector z i)) := by
  have hreal := Quaternion.star_eq_self.mp ((fiberCofactor_isHermitian w a z).apply none none)
  apply Matrix.ext
  intro i j
  rw [fiberCofactor_entry w a z hw ha hY i j, hreal]
  simp only [Matrix.smul_apply, OAI.Analysis.Calculus.Quaternion.outer, Quaternion.mul_coe_eq_smul, Quaternion.re_coe,
    smul_mul_assoc]

/-- The time coordinate is `(Y-S)/√2`, so this is precisely the rotated TT entry. -/
def fiberTimeComponent {d : ℕ} (w a : ℝ) (z : Index d → ℂ) : ℝ :=
  ((fiberCofactor w a z none none - fiberCofactor w a z none (some none) -
    fiberCofactor w a z (some none) none +
    fiberCofactor w a z (some none) (some none)).re) / 2

theorem fiberTimeComponent_formula {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hw : w ≠ 0) (ha : a ≠ 0) (hY : z none ≠ 0) :
    fiberTimeComponent w a z = (fiberCofactor w a z none none).re *
      Complex.normSq (fiberDenominator (ratio z)) / 2 := by
  unfold fiberTimeComponent
  rw [fiberCofactor_rankOne w a z hw ha hY]
  simp only [Matrix.smul_apply, OAI.Analysis.Calculus.Quaternion.outer, fiberKernelVector, map_one, star_one, one_mul, mul_one]
  simp only [complexK_apply_explicit]
  simp [fiberDenominator, Complex.normSq_apply]
  ring

theorem fiberTimeComponent_pos {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hw : w ≠ 0) (ha : a ≠ 0) (hY : z none ≠ 0)
    (hD : fiberDenominator (ratio z) ≠ 0) : 0 < fiberTimeComponent w a z := by
  rw [fiberTimeComponent_formula w a z hw ha hY]
  exact div_pos (mul_pos (fiberCofactor_YY_pos w a z hw ha hY)
    (Complex.normSq_pos.mpr hD)) (by norm_num)

theorem fiberTimeComponent_pos_on_fiber {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (ha : a ≠ 0) (hY : z none ≠ 0) (hr : fiberDefining (1 / 10) a z ≤ 0) :
    0 < fiberTimeComponent (1 / 10) a z :=
  fiberTimeComponent_pos _ a z (by norm_num) ha hY (fiberDenominator_ne_zero_on_fiber a z hr)

end OAI.Analysis.Calculus.Current
