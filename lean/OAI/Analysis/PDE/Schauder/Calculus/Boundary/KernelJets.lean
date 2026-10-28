import OAI.Analysis.PDE.Schauder.Calculus.Boundary.KernelIntegral

/-! Three actual derivatives of a weighted smooth kernel integral. -/

noncomputable section
open _root_.MeasureTheory Set Filter
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Green

universe u v
variable {E A F : Type u} {T : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace T] [CompactSpace T] [T2Space T] [SecondCountableTopology T]
  [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [IsFiniteMeasure μ]

local instance kernelJetFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance kernelJetFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance kernelJetSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance kernelJetSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance kernelJetThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance kernelJetThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance kernelJetFirstComplete : CompleteSpace (E →L[ℝ] F) := ContinuousLinearMap.instCompleteSpace
local instance kernelJetSecondComplete : CompleteSpace (E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.instCompleteSpace
local instance kernelJetThirdComplete : CompleteSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.instCompleteSpace

omit [CompleteSpace F] in
theorem weighted_kernel_integral_three_derivatives {U : Set E} (hU : IsOpen U)
    {Ω : Set (E × A)} (hΩ : IsOpen Ω) (K : E × A → F)
    (hK : ContDiffOn ℝ ∞ K Ω) (s : T → A) (hs : Continuous s)
    (w : T → ℝ) (hw : Continuous w)
    (hdom : ∀ x ∈ U, ∀ t, (x, s t) ∈ Ω) {x : E} (hx : x ∈ U) :
    let I := fun y => ∫ t, w t • K (y, s t) ∂μ
    fderiv ℝ I x = (∫ t, w t • OAI.Analysis.PDE.Green.partialFirstDerivative K (x, s t) ∂μ) ∧
    fderiv ℝ (fderiv ℝ I) x =
      (∫ t, w t • OAI.Analysis.PDE.Green.partialFirstDerivative (OAI.Analysis.PDE.Green.partialFirstDerivative K) (x, s t) ∂μ) ∧
    fderiv ℝ (fderiv ℝ (fderiv ℝ I)) x =
      (∫ t, w t • OAI.Analysis.PDE.Green.partialFirstDerivative (OAI.Analysis.PDE.Green.partialFirstDerivative (OAI.Analysis.PDE.Green.partialFirstDerivative K)) (x, s t) ∂μ) := by
  dsimp only
  let K₁ := OAI.Analysis.PDE.Green.partialFirstDerivative K
  let K₂ := OAI.Analysis.PDE.Green.partialFirstDerivative K₁
  have hK₁ := OAI.Analysis.PDE.Green.contDiffOn_partialFirstDerivative hΩ hK
  have hK₂ := OAI.Analysis.PDE.Green.contDiffOn_partialFirstDerivative hΩ hK₁
  have h₁ (y : E) (hy : y ∈ U) :=
    (hasFDerivAt_weighted_kernel_integral hU hΩ K hK s hs w hw hdom hy (μ := μ)).fderiv
  have h₂ (y : E) (hy : y ∈ U) :
      fderiv ℝ (fderiv ℝ (fun z => ∫ t, w t • K (z, s t) ∂μ)) y =
        ∫ t, w t • K₂ (y, s t) ∂μ := by
    have he : (fderiv ℝ (fun z => ∫ t, w t • K (z, s t) ∂μ)) =ᶠ[𝓝 y]
        (fun z => ∫ t, w t • K₁ (z, s t) ∂μ) := by
      filter_upwards [hU.mem_nhds hy] with z hz using h₁ z hz
    rw [he.fderiv_eq]
    exact (hasFDerivAt_weighted_kernel_integral hU hΩ K₁ hK₁ s hs w hw hdom hy (μ := μ)).fderiv
  refine ⟨h₁ x hx, h₂ x hx, ?_⟩
  have he : (fderiv ℝ (fderiv ℝ (fun z => ∫ t, w t • K (z, s t) ∂μ))) =ᶠ[𝓝 x]
      (fun z => ∫ t, w t • K₂ (z, s t) ∂μ) := by
    filter_upwards [hU.mem_nhds hx] with z hz using h₂ z hz
  rw [he.fderiv_eq]
  exact (hasFDerivAt_weighted_kernel_integral hU hΩ K₂ hK₂ s hs w hw hdom hx (μ := μ)).fderiv

omit [CompleteSpace F] [TopologicalSpace T] [CompactSpace T] [T2Space T] [SecondCountableTopology T] [BorelSpace T] in
theorem norm_weighted_integral_le (f : T → F) (w : T → ℝ) {M W : ℝ}
    (hf : ∀ t, ‖f t‖ ≤ M) (hw : ∀ t, |w t| ≤ W) (hM : 0 ≤ M) :
    ‖∫ t, w t • f t ∂μ‖ ≤ μ.real univ * (W * M) := by
  have hb : ∀ᵐ t ∂μ, ‖w t • f t‖ ≤ W * M := by
    filter_upwards with t
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hf t) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (hw t) hM)
  have hi := norm_integral_le_of_norm_le (integrable_const (W * M) (μ := μ)) hb
  simpa only [integral_const, smul_eq_mul] using hi

omit [CompleteSpace F] in
theorem exists_weighted_kernel_three_bound {U : Set E} (hU : IsOpen U)
    {Ω : Set (E × A)} (hΩ : IsOpen Ω) (K : E × A → F)
    (hK : ContDiffOn ℝ ∞ K Ω) (s : T → A) (hs : Continuous s)
    (hdom : ∀ x ∈ U, ∀ t, (x, s t) ∈ Ω) {x : E} (hx : x ∈ U) :
    ∃ C > 0, ∀ (w : T → ℝ), Continuous w → ∀ W, 0 ≤ W → (∀ t, |w t| ≤ W) →
      let I := fun y => ∫ t, w t • K (y, s t) ∂μ
      ‖fderiv ℝ I x‖ ≤ C * W ∧
      ‖fderiv ℝ (fderiv ℝ I) x‖ ≤ C * W ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I)) x‖ ≤ C * W := by
  have hsect {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
      (g : E × A → G) (hg : ContinuousOn g Ω) : Continuous (fun t => g (x, s t)) := by
    rw [← continuousOn_univ]
    exact hg.comp (continuous_const.prodMk hs).continuousOn (fun t _ => hdom x hx t)
  let K₁ := OAI.Analysis.PDE.Green.partialFirstDerivative K
  let K₂ := OAI.Analysis.PDE.Green.partialFirstDerivative K₁
  let K₃ := OAI.Analysis.PDE.Green.partialFirstDerivative K₂
  have hK₁ := OAI.Analysis.PDE.Green.contDiffOn_partialFirstDerivative hΩ hK
  have hK₂ := OAI.Analysis.PDE.Green.contDiffOn_partialFirstDerivative hΩ hK₁
  have hK₃ := OAI.Analysis.PDE.Green.contDiffOn_partialFirstDerivative hΩ hK₂
  obtain ⟨M₁, hM₁⟩ := isCompact_univ.exists_bound_of_continuousOn (hsect K₁ hK₁.continuousOn).continuousOn
  obtain ⟨M₂, hM₂⟩ := isCompact_univ.exists_bound_of_continuousOn (hsect K₂ hK₂.continuousOn).continuousOn
  obtain ⟨M₃, hM₃⟩ := isCompact_univ.exists_bound_of_continuousOn (hsect K₃ hK₃.continuousOn).continuousOn
  let M := |M₁| + |M₂| + |M₃| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hm₁ : ∀ t, ‖K₁ (x, s t)‖ ≤ M := by
    intro t
    have ht := hM₁ t (mem_univ t)
    dsimp [M]
    linarith [le_abs_self M₁, abs_nonneg M₂, abs_nonneg M₃]
  have hm₂ : ∀ t, ‖K₂ (x, s t)‖ ≤ M := by
    intro t
    have ht := hM₂ t (mem_univ t)
    dsimp [M]
    linarith [le_abs_self M₂, abs_nonneg M₁, abs_nonneg M₃]
  have hm₃ : ∀ t, ‖K₃ (x, s t)‖ ≤ M := by
    intro t
    have ht := hM₃ t (mem_univ t)
    dsimp [M]
    linarith [le_abs_self M₃, abs_nonneg M₁, abs_nonneg M₂]
  refine ⟨(μ.real univ + 1) * M, mul_pos (by positivity) hM, ?_⟩
  intro w hw W hW hsup
  dsimp only
  obtain ⟨h₁, h₂, h₃⟩ := weighted_kernel_integral_three_derivatives hU hΩ K hK s hs w hw hdom hx (μ := μ)
  rw [h₁, h₂, h₃]
  have hbound : μ.real univ * (W * M) ≤ (μ.real univ + 1) * M * W := by
    nlinarith [mul_nonneg hW hM.le]
  exact ⟨(norm_weighted_integral_le _ w hm₁ hsup hM.le).trans hbound,
    (norm_weighted_integral_le _ w hm₂ hsup hM.le).trans hbound,
    (norm_weighted_integral_le _ w hm₃ hsup hM.le).trans hbound⟩

end OAI.Analysis.PDE.Schauder
