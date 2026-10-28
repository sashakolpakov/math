import OAI.Analysis.Calculus.Quaternion.Bochner

/-! Differentiation of averages over a compact parameter space. -/

noncomputable section
namespace OAI.Analysis.Calculus.Quaternion

open _root_.MeasureTheory
open scoped Topology

variable {E F α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace α] [CompactSpace α] [T2Space α] [SecondCountableTopology α]
  [MeasurableSpace α] [BorelSpace α]
  {μ : Measure α} [IsFiniteMeasure μ]

omit [NormedSpace ℝ E] [ProperSpace E] [NormedSpace ℝ F] [CompleteSpace F] [CompactSpace α] [T2Space α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] in
theorem continuous_section_of_continuousOn {O : Set E} (A : E → α → F)
    (hA : ContinuousOn (Function.uncurry A) (O ×ˢ Set.univ)) {x : E} (hx : x ∈ O) :
    Continuous (A x) := by
  rw [← continuousOn_univ]
  exact hA.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ _ => ⟨hx, Set.mem_univ _⟩)

omit [CompleteSpace F] in
theorem hasFDerivAt_integral_compact {O : Set E} (ho : IsOpen O)
    (A : E → α → F) {x : E} (hx : x ∈ O)
    (hA : ContinuousOn (Function.uncurry A) (O ×ˢ Set.univ))
    (hDf : ContinuousOn (fun p : E × α => fderiv ℝ (fun y => A y p.2) p.1)
      (O ×ˢ Set.univ))
    (hD : ∀ y ∈ O, ∀ t, DifferentiableAt ℝ (fun z => A z t) y) :
    HasFDerivAt (fun y => ∫ t, A y t ∂μ) (∫ t, fderiv ℝ (fun y => A y t) x ∂μ) x := by
  obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (ho.mem_nhds hx)
  have hK : IsCompact (Metric.closedBall x ε ×ˢ (Set.univ : Set α)) :=
    (isCompact_closedBall x ε).prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hDf.mono (fun p hp => ⟨hsub hp.1, hp.2⟩))
  have hAc (y : E) (hy : y ∈ O) : Continuous (A y) :=
    continuous_section_of_continuousOn A hA hy
  have hDc : Continuous (fun t => fderiv ℝ (fun y => A y t) x) :=
    continuous_section_of_continuousOn (fun y t => fderiv ℝ (fun z => A z t) y) hDf hx
  have hAi : Integrable (A x) μ := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (hAc x hx).continuousOn.integrableOn_compact (μ := μ) isCompact_univ
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun y t => fderiv ℝ (fun z => A z t) y)
    (Metric.closedBall_mem_nhds x hε) ?_ hAi hDc.aestronglyMeasurable
      (bound := fun _ => C) ?_ (integrable_const C) ?_
  · filter_upwards [ho.mem_nhds hx] with y hy
    exact (hAc y hy).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t y hy => hC (y, t) ⟨hy, Set.mem_univ _⟩
  · exact Filter.Eventually.of_forall fun t y hy => (hD y (hsub hy) t).hasFDerivAt

theorem integral_fderiv_linear_zero_compact {O : Set E} (ho : IsOpen O)
    (A : E → α → F) {x : E} (hx : x ∈ O)
    (hA : ContinuousOn (Function.uncurry A) (O ×ˢ Set.univ))
    (hDf : ContinuousOn (fun p : E × α => fderiv ℝ (fun y => A y p.2) p.1)
      (O ×ˢ Set.univ))
    (hD : ∀ y ∈ O, ∀ t, DifferentiableAt ℝ (fun z => A z t) y)
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (L : (E →L[ℝ] F) →L[ℝ] Z)
    (hzero : ∀ᵐ t ∂μ, L (fderiv ℝ (fun y => A y t) x) = 0) :
    L (fderiv ℝ (fun y => ∫ t, A y t ∂μ) x) = 0 := by
  have hDiff := hasFDerivAt_integral_compact ho A hx hA hDf hD (μ := μ)
  have hDc : Continuous (fun t => fderiv ℝ (fun y => A y t) x) :=
    continuous_section_of_continuousOn (fun y t => fderiv ℝ (fun z => A z t) y) hDf hx
  have hDi : Integrable (fun t => fderiv ℝ (fun y => A y t) x) μ := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hDc.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
  rw [hDiff.fderiv, ← L.integral_comp_comm hDi]
  simpa using integral_congr_ae hzero

end OAI.Analysis.Calculus.Quaternion
