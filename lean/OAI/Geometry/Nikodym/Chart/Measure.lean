import OAI.Geometry.Nikodym.Definitions
import OAI.Geometry.Nikodym.Measurability

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Geometry.Nikodym

theorem eLpNorm_le_of_comparable_measure {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ ν : Measure X} (f : X → E) (p : ℝ≥0∞)
    {c : ℝ≥0∞} (hc : μ≤c • ν) :
    eLpNorm f p μ ≤ c ^ (1/p).toReal * eLpNorm f p ν := by
  exact (eLpNorm_mono_measure f hc).trans (eLpNorm_smul_measure_le c f p ν)

/-- Only the image of the chart needs a lower measure comparison. The
transported input is zero elsewhere, so no nonexistent global inverse is used. -/
theorem eLpNorm_le_of_comparable_measure_on {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ ν : Measure X} {V : Set X} (hV : MeasurableSet V)
    (f : X → E) (p : ℝ≥0∞) (hf : ∀ x∉V,f x=0)
    {c : ℝ≥0∞} (hc : μ.restrict V≤c • ν) :
    eLpNorm f p μ ≤ c ^ (1/p).toReal * eLpNorm f p ν := by
  have he : V.indicator f=f := by
    funext x
    by_cases hx : x∈V
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx,hf x hx]
  calc
    eLpNorm f p μ = eLpNorm f p (μ.restrict V) := by
      conv_lhs => rw [← he]
      exact eLpNorm_indicator_eq_eLpNorm_restrict hV
    _ ≤ _ := eLpNorm_le_of_comparable_measure f p hc

/-- The norm of a pulled-back function is controlled by the chart Jacobian
bound. This applies equally to a real, complex, or ENNReal-valued maximal output. -/
theorem eLpNorm_comp_le_of_map_le {X Y E : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [TopologicalSpace E] [ContinuousENorm E]
    {μ : Measure X} {ν : Measure Y} {F : X → Y} (hF : AEMeasurable F μ)
    (g : Y → E) (hg : AEStronglyMeasurable g (Measure.map F μ))
    (p : ℝ≥0∞) {c : ℝ≥0∞} (hc : Measure.map F μ≤c • ν) :
    eLpNorm (g ∘ F) p μ ≤ c ^ (1/p).toReal * eLpNorm g p ν := by
  rw [← eLpNorm_map_measure hg hF]
  exact (eLpNorm_mono_measure g hc).trans (eLpNorm_smul_measure_le c g p ν)

end OAI.Geometry.Nikodym
