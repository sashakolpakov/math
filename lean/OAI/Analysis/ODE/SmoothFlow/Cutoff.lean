import Mathlib

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff

namespace OAI.Analysis.ODE.SmoothFlow

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A locally smooth vector field has a genuine globally smooth,
compactly supported representative on a smaller closed ball. -/
theorem exists_global_smooth_agree {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f U) {x : E} (hx : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U ∧
      ∃ f₀ : E → F, ContDiff ℝ ∞ f₀ ∧ HasCompactSupport f₀ ∧
        EqOn f₀ f (closedBall x r) := by
  obtain ⟨d,hd,hdU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let β : ContDiffBump x :=
    { rIn := d/4
      rOut := d/2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hsupport : tsupport (β : E → ℝ) ⊆ U := by
    rw [β.tsupport_eq]
    intro y hy
    apply hdU
    exact (mem_closedBall.mp hy).trans_lt (by dsimp [β]; linarith)
  have hball : closedBall x (d/4) ⊆ U := by
    intro y hy
    apply hdU
    exact (mem_closedBall.mp hy).trans_lt (by linarith)
  refine ⟨d/4,by positivity,hball,(fun y => β y • f y),?_,?_,?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ U
    · exact β.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hy))
    · have hnot : y ∉ tsupport (β : E → ℝ) := fun h => hy (hsupport h)
      apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport (β : E → ℝ)).isOpen_compl.mem_nhds hnot] with z hz
      simp only [image_eq_zero_of_notMem_tsupport hz,zero_smul]
  · exact β.hasCompactSupport.smul_right
  · intro y hy
    change β y • f y = f y
    rw [β.one_of_mem_closedBall hy,one_smul]

end OAI.Analysis.ODE.SmoothFlow
