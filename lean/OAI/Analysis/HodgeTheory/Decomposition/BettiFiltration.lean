import OAI.Analysis.HodgeTheory.Decomposition.ComponentHarmonicClasses
import OAI.Analysis.HodgeTheory.Decomposition.HarmonicFiltration

/-! # Betti Filtration -/

namespace OAI.Analysis.HodgeTheory.Decomposition.BettiFiltration.Constructions

noncomputable section

/-! A closed filtered form has a filtered harmonic representative. Its pure
harmonic projections represent classes in exactly the selected Hodge pieces. -/

variable (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  [∀ C : irreducibleComponents X.carrier, MeasurableSpace (X.componentVariety C).analyticSpace]
  [∀ C : irreducibleComponents X.carrier, BorelSpace (X.componentVariety C).analyticSpace] (n : ℕ)

theorem harmonic_class_mem_hodge_sum (p : ℤ) (a : ComponentHarmonicTypes.Constructions.ComponentHarmonics X n)
    (ha : a.val ∈ Core.Constructions.filteredForms X (n + 1) p) :
    ComponentHarmonicClasses.Constructions.componentHarmonicBettiClass X n a ∈
      ⨆ (i : Core.Constructions.Bidegree (n + 1)) (_ : p ≤ (i.val.1 : ℤ)), Core.Constructions.hodgePiece X (n + 1) i := by
  rw [← ComponentHarmonicTypes.Constructions.sum_componentHarmonicProjection X n a]
  rw [map_sum]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : p ≤ (i.val.1 : ℤ)
  · apply Submodule.mem_iSup_of_mem i
    apply Submodule.mem_iSup_of_mem hi
    rw [ComponentHarmonicClasses.Constructions.hodgePiece_eq_harmonic_image]
    exact ⟨ComponentHarmonicTypes.Constructions.componentHarmonicProjection X n i a, ComponentHarmonicTypes.Constructions.componentHarmonicProjection_pure X n i a, rfl⟩
  · have hz : ComponentHarmonicTypes.Constructions.componentHarmonicProjection X n i a = 0 := by
      apply Subtype.ext
      exact HarmonicFiltration.Constructions.componentProjection_filtered_zero X (n + 1) p i hi a.val ha
    rw [hz, map_zero]
    exact Submodule.zero_mem _

theorem filtration_positive (p : ℤ) :
    Core.Constructions.deRhamFiltrationBetti X (n + 1) p =
      ⨆ (i : Core.Constructions.Bidegree (n + 1)) (_ : p ≤ (i.val.1 : ℤ)), Core.Constructions.hodgePiece X (n + 1) i := by
  apply le_antisymm _ (Core.Constructions.hodge_sum_le_filtration X (n + 1) p)
  rintro c ⟨a, ha, rfl⟩
  rw [← ComponentHarmonicClasses.Constructions.componentClosedHarmonicPart_class X n a]
  apply harmonic_class_mem_hodge_sum X n p
  exact HarmonicFiltration.Constructions.componentSmoothHarmonicPart_filtered X n p a.val ha

end

end OAI.Analysis.HodgeTheory.Decomposition.BettiFiltration.Constructions
