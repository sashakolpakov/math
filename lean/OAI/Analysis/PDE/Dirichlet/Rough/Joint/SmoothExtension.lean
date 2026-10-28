import OAI.Analysis.Calculus.SmoothExtension.HalfspaceExtension

noncomputable section
open Set Metric
open scoped ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Smoothness on a single closed half-patch yields one genuine smooth
extension near every boundary point, with a neighborhood independent of order. -/
theorem exists_smooth_extension_halfpatch
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    {O : Set E} (hO : IsOpen O) {x₀ : E} (hx₀ : x₀ ∈ O) (hxℓ : ℓ x₀ = 0)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f ({x | 0 ≤ ℓ x} ∩ O)) :
    ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ O ∧
      ∃ g : E → F, ContDiff ℝ ∞ g ∧ EqOn g f ({x | 0 ≤ ℓ x} ∩ V) := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hO x₀ hx₀
  have hm : MapsTo (fun z : E ↦ x₀+z) (ball 0 ε ∩ {x | 0 ≤ ℓ x})
      ({x | 0 ≤ ℓ x} ∩ O) := by
    intro z hz
    constructor
    · simpa only [Set.mem_ofPred_eq,map_add,hxℓ,zero_add] using hz.2
    · apply hball
      simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hz.1
  have hft : ContDiffOn ℝ ∞ (fun z : E ↦ f (x₀+z))
      (ball 0 ε ∩ {x | 0 ≤ ℓ x}) :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn hm
  obtain ⟨g,hg,hgeq⟩ := OAI.Analysis.Calculus.SmoothExtension.exists_smooth_extension_of_halfball ℓ ν hν
    (fun z : E ↦ f (x₀+z)) ε hε hft
  refine ⟨ball x₀ (ε/4),isOpen_ball,mem_ball_self (by positivity),?_,
    fun x ↦ g (x-x₀),hg.comp (contDiff_id.sub contDiff_const),?_⟩
  · exact (ball_subset_ball (by linarith)).trans hball
  · intro x hx
    have hxt : x-x₀ ∈ ball 0 (ε/4) ∩ {x | 0 ≤ ℓ x} := by
      constructor
      · simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hx.2
      · simpa only [Set.mem_ofPred_eq,map_sub,hxℓ,sub_zero] using hx.1
    simpa only [← add_sub_assoc,add_sub_cancel_left] using hgeq hxt

end OAI.Analysis.PDE.Dirichlet
