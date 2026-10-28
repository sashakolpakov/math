import OAI.Analysis.Normed.Function.Sobolev.HalfspaceCutoff
import OAI.Analysis.PDE.Weak.Elliptic.LocalDerivative

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

variable {d : ℕ}

def halfspaceTest (n : ℕ) (k : Fin d) (φ : (Fin d→ℝ)→ℝ) (x : Fin d→ℝ) : ℝ :=
  halfspaceGapCutoff n (x k)*φ x

theorem contDiff_halfspaceTest (n : ℕ) (k : Fin d) {φ : (Fin d→ℝ)→ℝ}
    (hφ : ContDiff ℝ 1 φ) : ContDiff ℝ 1 (halfspaceTest n k φ) :=
  (((contDiff_halfspaceGapCutoff n).of_le (by simp)).comp (contDiff_apply ℝ ℝ k)).mul hφ

theorem halfspaceTest_support (n : ℕ) (k : Fin d) (φ : (Fin d→ℝ)→ℝ) :
    tsupport (halfspaceTest n k φ)⊆{x|0<x k} := by
  have hs : tsupport (halfspaceTest n k φ)⊆{x | 1≤((n:ℝ)+1)*x k} := by
    apply closure_minimal _ (isClosed_le continuous_const (continuous_const.mul (continuous_apply k)))
    intro x hx
    by_contra hnot
    apply hx
    change halfspaceGapCutoff n (x k)*φ x=0
    rw [halfspaceGapCutoff_zero (le_of_not_ge hnot),zero_mul]
  intro x hx
  have h := hs hx
  have hn : 0<(n:ℝ)+1 := by positivity
  change 1≤((n:ℝ)+1)*x k at h
  change 0<x k
  nlinarith

theorem hasCompactSupport_halfspaceTest (n : ℕ) (k : Fin d) {φ : (Fin d→ℝ)→ℝ}
    (hs : HasCompactSupport φ) : HasCompactSupport (halfspaceTest n k φ) := hs.mul_left

theorem halfspaceTest_derivative (n : ℕ) (k : Fin d) {φ : (Fin d→ℝ)→ℝ}
    (hφ : ContDiff ℝ 1 φ) (x v : Fin d→ℝ) :
    fderiv ℝ (halfspaceTest n k φ) x v =
      halfspaceGapCutoff n (x k)*fderiv ℝ φ x v + halfspaceGapSlope n (x k)*v k*φ x := by
  have hc := (hasDerivAt_halfspaceGapCutoff n (x k)).comp_hasFDerivAt x
    (ContinuousLinearMap.proj k : (Fin d→ℝ)→L[ℝ] ℝ).hasFDerivAt
  have h := (hc.mul (hφ.differentiable one_ne_zero x).hasFDerivAt).fderiv
  have he := congrArg (fun L : (Fin d→ℝ)→L[ℝ] ℝ ↦ L v) h
  change fderiv ℝ (halfspaceTest n k φ) x v = _ at he
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,Function.comp_apply] at he
  rw [he]
  ring

/-- A C¹ test vanishing on the coordinate hyperplane is linearly small
in the distance to that hyperplane. -/
theorem abs_test_le_normal {φ : (Fin d→ℝ)→ℝ} (hφ : ContDiff ℝ 1 φ)
    (k : Fin d) (hzero : ∀x,x k=0→φ x=0) {L : ℝ} (hL : ∀x,‖fderiv ℝ φ x‖≤L)
    (x : Fin d→ℝ) : |φ x|≤L*|x k| := by
  let y := Function.update x k 0
  have hy : φ y=0 := hzero y (by simp [y])
  have he : x-y=x k • Pi.single k (1:ℝ) := by
    ext j
    by_cases hj : j=k
    · subst j
      simp [y]
    · simp [y,hj]
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z∈(univ : Set (Fin d→ℝ))) ↦ hφ.differentiable one_ne_zero z)
    (fun z _ ↦ hL z) (convex_univ : Convex ℝ (univ : Set (Fin d→ℝ)))
    (mem_univ y) (mem_univ x)
  rw [hy,sub_zero,he,norm_smul] at h
  simpa only [Pi.norm_single,norm_one,mul_one,Real.norm_eq_abs] using h

end OAI.Analysis.Normed.Function.Sobolev
