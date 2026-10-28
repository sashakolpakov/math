import OAI.Analysis.PDE.Nonlinear.LocalHolder

/-! A compactly supported C²,α localization with its genuine global Hölder jets. -/

noncomputable section
open Set Metric
open scoped Topology
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

local instance cutoffFirstGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance cutoffFirstSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance cutoffSecondGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance cutoffSecondSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def cutoffCommutator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ u : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  u x • fderiv ℝ (fderiv ℝ χ) x +
    (fderiv ℝ χ x).smulRight (fderiv ℝ u x) +
    (fderiv ℝ u x).smulRight (fderiv ℝ χ x)

theorem cutoff_hessian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ u : E → ℝ) (hχ : ContDiff ℝ 2 χ) (hu : ContDiff ℝ 2 u) (x : E) :
    fderiv ℝ (fderiv ℝ (fun y => χ y * u y)) x =
      χ x • fderiv ℝ (fderiv ℝ u) x + cutoffCommutator χ u x := by
  ext v w
  simp only [cutoffCommutator, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [OAI.Analysis.PDE.Dirichlet.hessian_mul hχ hu]
  ring

theorem contDiff_cutoffCommutator {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ u : E → ℝ) (hχ : ContDiff ℝ 3 χ) (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (cutoffCommutator χ u) := by
  have hDχ : ContDiff ℝ 2 (fderiv ℝ χ) := hχ.fderiv_right (by norm_num)
  have hDDχ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ χ)) := hDχ.fderiv_right (by norm_num)
  have hDu : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  exact (((hu.of_le (by norm_num)).smul hDDχ).add
    ((hDχ.of_le (by norm_num)).smulRight hDu)).add
    (hDu.smulRight (hDχ.of_le (by norm_num)))

theorem hasCompactSupport_cutoffCommutator {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ u : E → ℝ) (hχc : HasCompactSupport χ) :
    HasCompactSupport (cutoffCommutator χ u) := by
  apply hχc.mono'
  intro x hx
  by_contra hnot
  apply hx
  ext v w
  have hD : fderiv ℝ χ x = 0 := fderiv_of_notMem_tsupport ℝ hnot
  have hDD : fderiv ℝ (fderiv ℝ χ) x = 0 :=
    fderiv_of_notMem_tsupport ℝ (fun h => hnot (tsupport_fderiv_subset ℝ h))
  simp [cutoffCommutator, hD, hDD]

theorem exists_cutoff_hessian_holder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (χ u : E → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hu : ContDiff ℝ 2 u) (x₀ : E) {r R α C : ℝ}
    (hrR : r < R) (hR : 0 ≤ R) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hs : ∀ x, x ∉ closedBall x₀ r → χ x = 0)
    (hh : ∀ x ∈ closedBall x₀ R, ∀ y ∈ closedBall x₀ R,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * ‖x - y‖ ^ α) :
    ∃ H : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] E →L[ℝ] ℝ) α,
      ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ (fun y => χ y * u y)) x := by
  have hDD : Continuous (fderiv ℝ (fderiv ℝ u)) :=
    ((hu.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall x₀ R).exists_bound_of_continuousOn hDD.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ (mem_closedBall_self hR))
  obtain ⟨K, hK, _, hKh⟩ := OAI.Analysis.PDE.Schauder.compact_C1_holder χ (hχ.of_le (by norm_num)) hχc hα hα1
  have hprod : ∀ x ∈ closedBall x₀ R, ∀ y ∈ closedBall x₀ R,
      ‖χ x • fderiv ℝ (fderiv ℝ u) x - χ y • fderiv ℝ (fderiv ℝ u) y‖ ≤
        (C + K * M) * ‖x - y‖ ^ α := by
    intro x hx y hy
    have he : χ x • fderiv ℝ (fderiv ℝ u) x - χ y • fderiv ℝ (fderiv ℝ u) y =
        χ y • (fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y) +
        (χ x - χ y) • fderiv ℝ (fderiv ℝ u) x := by
      simp only [smul_sub, sub_smul]
      abel
    rw [he]
    calc
      _ ≤ ‖χ y • (fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y)‖ +
          ‖(χ x - χ y) • fderiv ℝ (fderiv ℝ u) x‖ := norm_add_le _ _
      _ = |χ y| * ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ +
          |χ x - χ y| * ‖fderiv ℝ (fderiv ℝ u) x‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * (C * ‖x - y‖ ^ α) + (K * ‖x - y‖ ^ α) * M := by
        apply add_le_add
        · apply mul_le_mul _ (hh x hx y hy) (norm_nonneg _) (by norm_num)
          rw [abs_of_nonneg (hχ01 y).1]
          exact (hχ01 y).2
        · exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hKh x y) (hM x hx)
            (norm_nonneg _) (by positivity)
      _ = _ := by ring
  obtain ⟨H, hH⟩ := exists_holder_of_support_separated
    (fun x => χ x • fderiv ℝ (fderiv ℝ u) x) (hχ.continuous.smul hDD)
    hχc.smul_right x₀ hrR hα (by positivity) (by intro x hx; rw [hs x hx, zero_smul]) hprod
  let B := OAI.Analysis.PDE.Schauder.compactC1Holder (cutoffCommutator χ u) (contDiff_cutoffCommutator χ u hχ hu)
    (hasCompactSupport_cutoffCommutator χ u hχc) hα hα1
  refine ⟨H + B, ?_⟩
  intro x
  change OAI.Analysis.Normed.Function.Holder.HolderMap.value H x + cutoffCommutator χ u x = _
  rw [hH x, cutoff_hessian χ u (hχ.of_le (by norm_num)) hu]

end OAI.Analysis.PDE.Nonlinear
