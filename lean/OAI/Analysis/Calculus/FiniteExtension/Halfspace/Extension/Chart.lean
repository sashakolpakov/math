import OAI.Analysis.Calculus.FiniteExtension.Halfspace.Extension.Ball

/-! Passing from a one-sided boundary chart to a genuine classical
extension on a physical neighborhood. -/

noncomputable section
open Set Metric
open scoped ContDiff
namespace OAI.Analysis.Calculus.FiniteExtension

variable {m N : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- Only one-sided Cᴺ regularity of the physical function is required.
The chart is used for reflection and its inverse transports the resulting
global Cᴺ function back to the original coordinates. -/
theorem exists_contDiff_extension_in_chart
    (k : Fin m) (r : E → ℝ) (f : E → F)
    (hf : ContDiffOn ℝ N f {x | r x ≤ 0})
    (G P : E → E) (hG : ContDiff ℝ N G) (hP : ContDiff ℝ N P)
    {a : E} (hPa : P a = 0) {U V : Set E}
    (hU : IsOpen U) (h0U : 0 ∈ U) (hV : IsOpen V) (haV : a ∈ V)
    (hGP : ∀ x ∈ V, G (P x) = x)
    (hside : ∀ z ∈ U, r (G z) ≤ 0 ↔ 0 ≤ z k) :
    ∃ W : Set E, IsOpen W ∧ a ∈ W ∧
      ∃ g : E → F, ContDiff ℝ N g ∧ ∀ x ∈ W, r x ≤ 0 → g x = f x := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  have hfg : ContDiffOn ℝ N (fun z => f (G z))
      ({z | 0 ≤ z k} ∩ ball 0 R) := by
    exact hf.comp hG.contDiffOn (fun z hz => (hside z (hRU hz.2)).mpr hz.1)
  obtain ⟨g, hg, hgeq⟩ := exists_contDiff_extension_coordinate_halfball k hR
    (fun z => f (G z)) hfg
  refine ⟨V ∩ P ⁻¹' ball 0 (R/2), hV.inter (isOpen_ball.preimage hP.continuous),
    ⟨haV, ?_⟩, fun x => g (P x), hg.comp hP, ?_⟩
  · simpa only [mem_preimage, hPa, mem_ball, dist_self] using (show 0 < R/2 by positivity)
  · intro x hx hxr
    have hxU : P x ∈ U := hRU (ball_subset_ball (by linarith) hx.2)
    have hpos : 0 ≤ P x k := (hside (P x) hxU).mp (by simpa only [hGP x hx.1] using hxr)
    exact (hgeq ⟨hpos, ball_subset_closedBall hx.2⟩).trans (congrArg f (hGP x hx.1))

end OAI.Analysis.Calculus.FiniteExtension
