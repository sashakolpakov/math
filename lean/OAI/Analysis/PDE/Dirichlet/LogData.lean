import OAI.Analysis.PDE.Dirichlet.Boundary.Tangential
import OAI.Analysis.PDE.Dirichlet.DataGradient

open Set Filter
open scoped Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

theorem second_deriv_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (v : E) :
    deriv (deriv (fun t : ℝ ↦ f (x + t • v))) 0 = fderiv ℝ (fderiv ℝ f) x v v := by
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ ↦ x + s • v) v t := by
    intro t
    simpa using (((hasDerivAt_id t).smul_const v).const_add x)
  have ht : Tendsto (fun t : ℝ ↦ x + t • v) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul, add_zero] using (hline 0).continuousAt.tendsto
  have hnear := ht.eventually (hf.eventually (by norm_num))
  have heq : deriv (fun t : ℝ ↦ f (x + t • v)) =ᶠ[𝓝 0]
      fun t ↦ fderiv ℝ f (x + t • v) v := by
    filter_upwards [hnear] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hline t)).deriv
  rw [heq.deriv_eq]
  have hD := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hl : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := hline 0
  have hD' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (x + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using hD.hasFDerivAt
  have hcomp : HasDerivAt (fun t : ℝ ↦ fderiv ℝ f (x + t • v))
      (fderiv ℝ (fderiv ℝ f) x v) 0 := by
    exact hD'.comp_hasDerivAt 0 hl
  simpa only [zero_smul, add_zero, add_zero, map_zero] using
    (hcomp.clm_apply (hasDerivAt_const (0 : ℝ) v)).deriv

/-- Compact positivity of the prescribed density gives the uniform second
directional lower bound for its logarithm needed by the interior estimate. -/
theorem exists_log_second_directional_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {K : Set E} (hK : IsCompact K) (hpos : ∀ x ∈ K, 0 < F x) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ v : E,
      -L * ‖v‖ ^ 2 ≤ deriv (deriv (fun t : ℝ ↦ Real.log (F (x + t • v)))) 0 := by
  have hloc : ∀ x ∈ K, ContDiffAt ℝ 2 (fun z ↦ Real.log (F z)) x := by
    intro x hx
    exact hF.contDiffAt.log (hpos x hx).ne'
  have hc : ContinuousOn (fun x ↦ ‖fderiv ℝ (fderiv ℝ (fun z ↦ Real.log (F z))) x‖) K := by
    intro x hx
    exact (((hloc x hx).fderiv_right (m := 1) (by norm_num)).fderiv_right
      (m := 0) (by norm_num)).continuousAt.norm.continuousWithinAt
  obtain ⟨D, hD⟩ := hK.bddAbove_image hc
  let L := max D 0 + 1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro x hx v
  rw [second_deriv_line (hloc x hx)]
  have hb : ‖fderiv ℝ (fderiv ℝ (fun z ↦ Real.log (F z))) x‖ ≤ L :=
    (hD (mem_image_of_mem _ hx)).trans (by dsimp [L]; linarith [le_max_left D 0])
  have h := (bilinear_abs_le (fderiv ℝ (fderiv ℝ (fun z ↦ Real.log (F z))) x) v v).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (norm_nonneg v)) (norm_nonneg v))
  have hlow := (neg_abs_le (fderiv ℝ (fderiv ℝ (fun z ↦ Real.log (F z))) x v v))
  nlinarith

end OAI.Analysis.PDE.Dirichlet
