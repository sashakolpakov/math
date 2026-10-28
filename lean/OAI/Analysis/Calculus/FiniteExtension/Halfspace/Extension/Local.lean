import OAI.Analysis.Calculus.FiniteExtension.Halfspace.Extension

/-! Localizing the classical reflection construction before extension. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.Calculus.FiniteExtension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_cutoff_smul {N : ℕ} {s U : Set E} (hU : IsOpen U)
    (f : E → F) (hf : ContDiffOn ℝ N f (s ∩ U))
    (η : E → ℝ) (hη : ContDiff ℝ N η) (hsupport : tsupport η ⊆ U) :
    ContDiffOn ℝ N (fun x => η x • f x) s := by
  intro x hx
  by_cases hxU : x ∈ U
  · have hfx : ContDiffWithinAt ℝ N f s x :=
      (contDiffWithinAt_inter (hU.mem_nhds hxU)).mp (hf x ⟨hx, hxU⟩)
    exact hη.contDiffAt.contDiffWithinAt.smul hfx
  · have hnot : x ∉ tsupport η := fun h => hxU (hsupport h)
    have he : (fun y => η y • f y) =ᶠ[𝓝 x] (fun _ => (0 : F)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with y hy
      simp only [hy, Pi.zero_apply, zero_smul]
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

theorem exists_contDiff_extension_of_local_halfspace {N : ℕ}
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    {U : Set E} (hU : IsOpen U) (f : E → F)
    (hf : ContDiffOn ℝ N f ({x | 0 ≤ ℓ x} ∩ U))
    (η : E → ℝ) (hη : ContDiff ℝ N η) (hsupport : tsupport η ⊆ U) :
    ∃ g : E → F, ContDiff ℝ N g ∧
      ∀ x, 0 ≤ ℓ x → η x = 1 → g x = f x := by
  obtain ⟨g, hg, heq⟩ := exists_contDiff_extension_of_contDiffOn_halfspace ℓ ν hν
    (fun x => η x • f x) (contDiffOn_cutoff_smul hU f hf η hη hsupport)
  refine ⟨g, hg, ?_⟩
  intro x hx hηx
  simpa only [hηx, one_smul] using heq hx

end OAI.Analysis.Calculus.FiniteExtension
