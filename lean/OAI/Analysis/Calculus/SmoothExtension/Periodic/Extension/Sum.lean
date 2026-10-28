import OAI.Analysis.PDE.Variational.Periodization

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Calculus.SmoothExtension

open OAI.Analysis.PDE.Variational

variable {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup T]

theorem contDiff_discretePeriodization_order (L : T →+ E)
    (hL : ∀R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {φ : E → ℝ} {q : ℕ} (hφ : ContDiff ℝ q φ) (hc : HasCompactSupport φ) :
    ContDiff ℝ q (OAI.Analysis.PDE.Variational.discretePeriodization L φ) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨U,hU,hfin⟩ := OAI.Analysis.PDE.Variational.locallyFinite_discrete_translates L hL hc x
  have heq : OAI.Analysis.PDE.Variational.discretePeriodization L φ =ᶠ[𝓝 x]
      (fun y ↦ ∑z ∈ hfin.toFinset, φ (y + L z)) := by
    filter_upwards [hU] with y hy
    apply tsum_eq_sum
    intro z hz
    by_contra hne
    exact hz (hfin.mem_toFinset.mpr ⟨y,hne,hy⟩)
  have hs : ContDiff ℝ q (fun y ↦ ∑z ∈ hfin.toFinset, φ (y + L z)) :=
    ContDiff.sum (fun z _ ↦ hφ.comp (contDiff_id.add contDiff_const))
  exact hs.contDiffAt.congr_of_eventuallyEq heq

omit [NormedSpace ℝ E] in
theorem summable_discrete_translates (L : T →+ E)
    (hL : ∀R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {φ : E → ℝ} (hc : HasCompactSupport φ) (x : E) :
    Summable (fun z ↦ φ (x + L z)) := by
  have hf : (Function.support (fun z ↦ φ (x + L z))).Finite :=
    (OAI.Analysis.PDE.Variational.locallyFinite_discrete_translates L hL hc).point_finite x
  exact summable_of_hasFiniteSupport hf

def smoothReciprocal (t : ℝ) : ℝ := Real.smoothTransition (2*t-1) / t

theorem contDiff_smoothReciprocal : ContDiff ℝ ∞ smoothReciprocal := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t = 0
  · subst t
    have he : smoothReciprocal =ᶠ[𝓝 (0 : ℝ)] (fun _ ↦ 0) := by
      filter_upwards [gt_mem_nhds (show (0 : ℝ) < 1/2 by norm_num)] with y hy
      simp [smoothReciprocal,Real.smoothTransition.zero_of_nonpos (show 2*y-1 ≤ 0 by linarith)]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact ((Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)).contDiffAt.div
      contDiffAt_id ht)

theorem smoothReciprocal_mul {t : ℝ} (ht : 1 ≤ t) : smoothReciprocal t * t = 1 := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht)
  simp [smoothReciprocal,Real.smoothTransition.one_of_one_le (show 1 ≤ 2*t-1 by linarith),ht0]

end OAI.Analysis.Calculus.SmoothExtension
