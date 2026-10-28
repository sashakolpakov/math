import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierTools

/-! # One Coordinate -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.OneCoordinate.LocalAnalysis

noncomputable section

/-! The one-coordinate position measure and Fourier integral agree with
their scalar-field counterparts. -/

open _root_.MeasureTheory

theorem integral_one_coordinate {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (f : α → E) :
    (∫ x : Fin 1 → α, f (x 0) ∂(Measure.pi (fun _ : Fin 1 => μ))) = ∫ t, f t ∂μ :=
  (measurePreserving_funUnique μ (Fin 1)).integral_comp
    (MeasurableEquiv.funUnique (Fin 1) α).measurableEmbedding f

theorem measure_one_coordinate {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {S : Set α} (hS : MeasurableSet S) :
    (Measure.pi (fun _ : Fin 1 => μ)) {x | x 0 ∈ S} = μ S :=
  (measurePreserving_funUnique μ (Fin 1)).measure_preimage hS.nullMeasurableSet

theorem compact_one_coordinate {α : Type*} [TopologicalSpace α]
    {S : Set α} (hS : IsCompact S) : IsCompact {x : Fin 1 → α | x 0 ∈ S} := by
  have he : {x : Fin 1 → α | x 0 ∈ S} = Set.univ.pi (fun _ : Fin 1 => S) := by
    ext x
    simp [Set.mem_pi, Fin.forall_fin_one]
  rw [he]
  simpa [Set.pi] using (isCompact_pi_infinite fun _ : Fin 1 => hS)

theorem fourierIntegral_one_coordinate
    {k : Type} [Field k] [MeasurableSpace k]
    (ψ : AddChar k ℂ) (μ : Measure k) (f : k → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position k 1) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin 1 => μ)) (fun y => f (y 0)) x =
      ∫ t, f t * ψ (-(x 0 * t)) ∂μ := by
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  simp only [Local.FunctionsMetaplectic.Construction.dot, Fin.sum_univ_one]
  exact integral_one_coordinate μ (fun t => f t * ψ (-(x 0 * t)))

theorem referenceFourier_one_coordinate
    (k : Type) [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k]
    (ψ : AddChar k ℂ) (x : Local.FunctionsMetaplectic.Construction.Position k 1) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin 1 => (Measure.addHaar : Measure k)))
      (({y : Local.FunctionsMetaplectic.Construction.Position k 1 | y 0 ∈ (Local.FunctionsMetaplectic.Construction.referenceCompact k : Set k)} : Set (Local.FunctionsMetaplectic.Construction.Position k 1)).indicator
        (fun _ => (1 : ℂ))) x = Local.FunctionsMetaplectic.Construction.referenceFourier k ψ (x 0) := by
  have he : ({y : Local.FunctionsMetaplectic.Construction.Position k 1 | y 0 ∈ (Local.FunctionsMetaplectic.Construction.referenceCompact k : Set k)} : Set (Local.FunctionsMetaplectic.Construction.Position k 1)).indicator
      (fun _ => (1 : ℂ)) =
      fun y => (Local.FunctionsMetaplectic.Construction.referenceCompact k : Set k).indicator (fun _ => (1 : ℂ)) (y 0) := by
    funext y
    by_cases hy : y 0 ∈ (Local.FunctionsMetaplectic.Construction.referenceCompact k : Set k)
    · simp only [Set.indicator_of_mem hy]
      exact ite_eq_left hy
    · simp only [Set.indicator_of_notMem hy]
      exact ite_eq_right hy
  rw [he, fourierIntegral_one_coordinate, Local.FunctionsMetaplectic.Construction.referenceFourier,
    ← integral_indicator (Local.FunctionsMetaplectic.Construction.referenceCompact k).isCompact.measurableSet]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    by_cases ht : t ∈ (Local.FunctionsMetaplectic.Construction.referenceCompact k : Set k) <;> simp [ht]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.OneCoordinate.LocalAnalysis
