import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.TensorMetricTest

/-! # Squared Real Cutoff -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SquaredRealCutoff

noncomputable section

/-! Exact smoothness, support and derivative formulas for the square of a real chart cutoff. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def squaredRealCutoff (η : E → ℝ) (x : E) : ℂ := (η x : ℂ) ^ 2

theorem squaredRealCutoff_smooth (η : E → ℝ) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (squaredRealCutoff η) := (Complex.ofRealCLM.contDiff.comp hη).pow 2

omit [NormedSpace ℝ E] in
theorem squaredRealCutoff_tsupport (η : E → ℝ) : tsupport (squaredRealCutoff η) ⊆ tsupport η := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  simp only [squaredRealCutoff, hx, Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0)]

omit [NormedSpace ℝ E] in
theorem squaredRealCutoff_hasCompactSupport (η : E → ℝ) (hη : HasCompactSupport η) :
    HasCompactSupport (squaredRealCutoff η) :=
  hη.isCompact.of_isClosed_subset (isClosed_tsupport _) (squaredRealCutoff_tsupport η)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem squaredRealCutoff_re (η : E → ℝ) (x : E) : (squaredRealCutoff η x).re = η x ^ 2 := by
  simp only [squaredRealCutoff, ← Complex.ofReal_pow, Complex.ofReal_re]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem squaredRealCutoff_im (η : E → ℝ) (x : E) : (squaredRealCutoff η x).im = 0 := by
  simp only [squaredRealCutoff, ← Complex.ofReal_pow, Complex.ofReal_im]

theorem squaredRealCutoff_fderiv (η : E → ℝ) {x : E} (hη : DifferentiableAt ℝ η x) (v : E) :
    fderiv ℝ (squaredRealCutoff η) x v = 2 * (η x : ℂ) * (fderiv ℝ η x v : ℂ) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x hη.hasFDerivAt
  have hv := congrArg (fun T : E →L[ℝ] ℂ => T v) (hd.mul hd).fderiv
  change fderiv ℝ (fun y => (η y : ℂ) * (η y : ℂ)) x v = _ at hv
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    Function.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul] at hv
  have heq : squaredRealCutoff η = (fun y => (η y : ℂ) * (η y : ℂ)) := funext (fun y => pow_two _)
  rw [heq, hv]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SquaredRealCutoff
