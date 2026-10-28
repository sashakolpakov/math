import OAI.Analysis.Calculus.SmoothExtension.HalfspaceExtension

/-! Infinite-order halfspace extension in fixed smooth boundary charts. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace OAI.Analysis.Calculus.SmoothExtension

variable {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local notation "E" => EuclideanSpace ℝ (Fin m)

theorem exists_smooth_extension_in_chart
    (k : Fin m) (r : E → ℝ) (f : E → F)
    (hf : ContDiffOn ℝ ∞ f {x | r x ≤ 0})
    (G P : E → E) (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    {a : E} (hPa : P a = 0) {U V : Set E}
    (hU : IsOpen U) (h0U : 0 ∈ U) (hV : IsOpen V) (haV : a ∈ V)
    (hGP : ∀ x ∈ V, G (P x) = x)
    (hside : ∀ z ∈ U, r (G z) ≤ 0 ↔ 0 ≤ z k) :
    ∃ W : Set E, IsOpen W ∧ a ∈ W ∧
      ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ x ∈ W, r x ≤ 0 → g x = f x := by
  obtain ⟨R,hR,hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  have hfg : ContDiffOn ℝ ∞ (fun z => f (G z))
      (ball 0 R ∩ {z | 0 ≤ z k}) :=
    hf.comp hG.contDiffOn (fun z hz => (hside z (hRU hz.1)).mpr hz.2)
  obtain ⟨g,hg,hgeq⟩ := exists_smooth_extension_of_halfball
    (EuclideanSpace.proj k) (EuclideanSpace.single k 1) (by simp)
    (fun z => f (G z)) R hR hfg
  refine ⟨V ∩ P ⁻¹' ball 0 (R/4), hV.inter (isOpen_ball.preimage hP.continuous),
    ⟨haV,?_⟩, fun x => g (P x),hg.comp hP,?_⟩
  · simpa only [mem_preimage,hPa,mem_ball,dist_self] using (show 0<R/4 by positivity)
  · intro x hx hxr
    have hxU : P x ∈ U := hRU (ball_subset_ball (by linarith) hx.2)
    have hpos : 0 ≤ P x k := (hside (P x) hxU).mp (by simpa only [hGP x hx.1] using hxr)
    exact (hgeq ⟨hx.2,hpos⟩).trans (congrArg f (hGP x hx.1))

end OAI.Analysis.Calculus.SmoothExtension
