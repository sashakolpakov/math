import OAI.Analysis.PDE.Dirichlet.Periodic.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Basic

open Set Filter Module
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

/-- Extend an interior zero-boundary function by zero outside the negative sublevel. -/
def zeroBoundaryExtension {E : Type*} (r v : E → ℝ) (x : E) : ℝ := by
  classical
  exact if r x < 0 then v x else 0

theorem zeroBoundaryExtension_of_neg {E : Type*} {r v : E → ℝ} {x : E}
    (hx : r x < 0) : zeroBoundaryExtension r v x = v x := by
  simp [zeroBoundaryExtension, hx]

theorem zeroBoundaryExtension_of_nonneg {E : Type*} {r v : E → ℝ} {x : E}
    (hx : 0 ≤ r x) : zeroBoundaryExtension r v x = 0 := by
  simp [zeroBoundaryExtension, not_lt.mpr hx]

theorem norm_zeroBoundaryExtension_le {E : Type*} {r v : E → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hv : ∀ x, r x < 0 → ‖v x‖ ≤ C * ‖r x‖) (x : E) :
    ‖zeroBoundaryExtension r v x‖ ≤ C * ‖r x‖ := by
  by_cases hx : r x < 0
  · rw [zeroBoundaryExtension_of_neg hx]
    exact hv x hx
  · rw [zeroBoundaryExtension_of_nonneg (not_lt.mp hx), norm_zero]
    positivity

/-- The scalar barriers provide the boundary continuity that interior compactness
alone does not supply. -/
theorem continuous_zeroBoundaryExtension {E : Type*} [TopologicalSpace E]
    {r v : E → ℝ} (hr : Continuous r) (hv : ContinuousOn v {x | r x < 0})
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, r x < 0 → ‖v x‖ ≤ C * ‖r x‖) :
    Continuous (zeroBoundaryExtension r v) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_trichotomy (r x) 0 with hx | hx | hx
  · apply (hv.continuousAt ((isOpen_lt hr continuous_const).mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt hr continuous_const).mem_nhds hx] with y hy
    exact zeroBoundaryExtension_of_neg hy
  · have hlim : Tendsto (fun y ↦ C * ‖r y‖) (𝓝 x) (𝓝 0) := by
      simpa only [hx, norm_zero, mul_zero] using
        (tendsto_const_nhds.mul hr.continuousAt.norm :
          Tendsto (fun y ↦ C * ‖r y‖) (𝓝 x) (𝓝 (C * ‖r x‖)))
    have hz : zeroBoundaryExtension r v x = 0 := zeroBoundaryExtension_of_nonneg hx.ge
    rw [ContinuousAt, hz]
    exact squeeze_zero_norm (norm_zeroBoundaryExtension_le hC hbound) hlim
  · apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const hr).mem_nhds hx] with y hy
    exact zeroBoundaryExtension_of_nonneg hy.le

theorem zeroBoundaryExtension_barriers {E : Type*} {r v : E → ℝ} {b B : ℝ}
    (hv : ∀ x, r x < 0 → B * r x ≤ v x ∧ v x ≤ b * r x)
    {x : E} (hx : r x ≤ 0) :
    B * r x ≤ zeroBoundaryExtension r v x ∧ zeroBoundaryExtension r v x ≤ b * r x := by
  rcases hx.eq_or_lt with hx | hx
  · simp [zeroBoundaryExtension, hx]
  · rw [zeroBoundaryExtension_of_neg hx]
    exact hv x hx

theorem continuous_zeroBoundaryExtension_of_barriers {E : Type*} [TopologicalSpace E]
    {r v : E → ℝ} (hr : Continuous r) (hv : ContinuousOn v {x | r x < 0})
    {b B : ℝ} (hb : 0 ≤ b) (hbB : b ≤ B)
    (hbound : ∀ x, r x < 0 → B * r x ≤ v x ∧ v x ≤ b * r x) :
    Continuous (zeroBoundaryExtension r v) := by
  apply continuous_zeroBoundaryExtension hr hv (hb.trans hbB)
  intro x hx
  have hneg : v x ≤ 0 := (hbound x hx).2.trans (mul_nonpos_of_nonneg_of_nonpos hb hx.le)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos hneg, abs_of_neg hx]
  nlinarith [(hbound x hx).1]

theorem tendsto_zeroBoundaryExtension {E : Type*} {r v : E → ℝ} {u : ℕ → E → ℝ}
    (hlim : ∀ x, r x < 0 → Tendsto (fun k ↦ u k x) atTop (𝓝 (v x)))
    (hzero : ∀ k x, r x = 0 → u k x = 0) {x : E} (hx : r x ≤ 0) :
    Tendsto (fun k ↦ u k x) atTop (𝓝 (zeroBoundaryExtension r v x)) := by
  rcases hx.eq_or_lt with hx | hx
  · have hu : (fun k ↦ u k x) = fun _ ↦ (0 : ℝ) := funext (fun k ↦ hzero k x hx)
    rw [hu, zeroBoundaryExtension_of_nonneg hx.ge]
    exact tendsto_const_nhds
  · rw [zeroBoundaryExtension_of_neg hx]
    exact hlim x hx

theorem latticePeriodic_zeroBoundaryExtension_of_limit
    {E P V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P} {r v : E → ℝ} {u : ℕ → E → ℝ}
    (hr : LatticePeriodic e lat r) (hu : ∀ k, LatticePeriodic e lat (u k))
    (hlim : ∀ x, r x < 0 → Tendsto (fun k ↦ u k x) atTop (𝓝 (v x))) :
    LatticePeriodic e lat (zeroBoundaryExtension r v) := by
  intro x l
  have hrx := hr x l
  by_cases hx : r x < 0
  · have hy : r (e.symm ((e x).1 + (l : P), (e x).2)) < 0 := by rwa [hrx]
    rw [zeroBoundaryExtension_of_neg hx, zeroBoundaryExtension_of_neg hy]
    apply tendsto_nhds_unique (hlim _ hy)
    have huseq : (fun k ↦ u k (e.symm ((e x).1 + (l : P), (e x).2))) =
        fun k ↦ u k x := funext (fun k ↦ hu k x l)
    rw [huseq]
    exact hlim x hx
  · rw [zeroBoundaryExtension_of_nonneg (not_lt.mp hx),
      zeroBoundaryExtension_of_nonneg (by simpa only [hrx] using not_lt.mp hx)]

end OAI.Analysis.PDE.Dirichlet
