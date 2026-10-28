import OAI.Analysis.HodgeTheory.Decomposition.ComponentHarmonic

/-! # Harmonic Filtration -/

namespace OAI.Analysis.HodgeTheory.Decomposition.HarmonicFiltration.Constructions

noncomputable section

/-! The actual smooth harmonic representative preserves the filtration
defined on forms before passage to cohomology. -/

theorem componentProjection_filtered_zero (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (p : ℤ) (j : Core.Constructions.Bidegree n) (hj : ¬p ≤ (j.val.1 : ℤ))
    (a : X.componentForms n) (ha : a ∈ Core.Constructions.filteredForms X n p) : Projectors.Constructions.componentProjection X n j a = 0 := by
  have hker : Core.Constructions.filteredForms X n p ≤ (Projectors.Constructions.componentProjection X n j).ker := by
    unfold Core.Constructions.filteredForms
    refine iSup_le fun i => iSup_le fun hi => ?_
    intro f hf
    change Projectors.Constructions.componentProjection X n j f = 0
    have hji : j ≠ i := by rintro rfl; exact hj hi
    rw [ComponentRotation.Constructions.componentProjection_on_pure X n j i f hf, ite_eq_right hji]
  exact hker ha

variable (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  [∀ C : irreducibleComponents X.carrier, MeasurableSpace (X.componentVariety C).analyticSpace]
  [∀ C : irreducibleComponents X.carrier, BorelSpace (X.componentVariety C).analyticSpace] (n : ℕ)

theorem componentSmoothHarmonicPart_filtered (p : ℤ) (a : X.componentForms (n + 1))
    (ha : a ∈ Core.Constructions.filteredForms X (n + 1) p) :
    ComponentHarmonic.Constructions.componentSmoothHarmonicPart X n a ∈ Core.Constructions.filteredForms X (n + 1) p := by
  rw [← Projectors.Constructions.sum_componentProjection X (n + 1) (ComponentHarmonic.Constructions.componentSmoothHarmonicPart X n a)]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : p ≤ (i.val.1 : ℤ)
  · apply Submodule.mem_iSup_of_mem i
    apply Submodule.mem_iSup_of_mem hi
    exact Projectors.Constructions.componentProjection_pure X (n + 1) i _
  · rw [ComponentHarmonic.Constructions.componentSmoothHarmonicPart_projection_zero X n i a (componentProjection_filtered_zero X (n + 1) p i hi a ha)]
    exact (Core.Constructions.filteredForms X (n + 1) p).zero_mem

end

end OAI.Analysis.HodgeTheory.Decomposition.HarmonicFiltration.Constructions
