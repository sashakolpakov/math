import OAI.Geometry.Nikodym.FullStrip

noncomputable section
open _root_.MeasureTheory Set
open scoped ENNReal
namespace OAI.Geometry.Nikodym

theorem lintegral_le_sum_of_finite_cover {X I : Type*} [MeasurableSpace X]
    {μ : Measure X} {s : Set X} {u : I → Set X} (t : Finset I)
    (hs : MeasurableSet s) (hu : ∀ i ∈ t, MeasurableSet (u i)) {F : X → ℝ≥0∞} (hF : Measurable F)
    (hcover : ∀ x ∈ s, ∃ i ∈ t, x ∈ u i) :
    (∫⁻ x in s, F x ∂μ) ≤ ∑ i ∈ t, ∫⁻ x in u i, F x ∂μ := by
  calc
    _ ≤ ∫⁻ x, ∑ i ∈ t, (u i).indicator F x ∂μ := by
      rw [← lintegral_indicator hs]
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ s
      · rw [indicator_of_mem hx]
        obtain ⟨i,hi,hxi⟩ := hcover x hx
        calc
          F x = (u i).indicator F x := (indicator_of_mem hxi F).symm
          _ ≤ ∑ j ∈ t, (u j).indicator F x :=
            Finset.single_le_sum (f:=fun j => (u j).indicator F x) (fun _ _ => bot_le) hi
      · simp only [indicator_of_notMem hx]; exact bot_le
    _ = _ := by
      rw [MeasureTheory.lintegral_finsetSum t (fun i hi => hF.indicator (hu i hi))]
      apply Finset.sum_congr rfl
      intro i hi
      exact lintegral_indicator (hu i hi) F

end OAI.Geometry.Nikodym
