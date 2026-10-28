import Mathlib

/-! # Density Pushforward -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.DensityPushforward.Construction

noncomputable section

/-! Change of variables for densities, and normalization of a measure
whose translates are scaled by a positive character. -/

open _root_.MeasureTheory
open scoped NNReal ENNReal

theorem map_comap_of_embedding
    {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Y) (f : X → Y) (hf : MeasurableEmbedding f) :
    (μ.comap f).map f = μ.restrict (Set.range f) := by
  ext S hS
  rw [Measure.map_apply hf.measurable hS,
    Measure.comap_apply f hf.injective (fun _ => hf.measurableSet_image.mpr) μ (hf.measurable hS),
    Measure.restrict_apply hS, Set.image_preimage_eq_inter_range]

theorem map_withDensity_pullback
    {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → Y) (hf : Measurable f)
    (w : Y → ℝ≥0∞) (hw : Measurable w) :
    (μ.withDensity (w ∘ f)).map f = (μ.map f).withDensity w := by
  ext S hS
  rw [Measure.map_apply hf hS, withDensity_apply _ (hf hS),
    withDensity_apply _ hS, setLIntegral_map hS hw hf]
  rfl

theorem character_weight_invariant
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) (ρ : G →* ℝ≥0) (hρ : Measurable ρ) (hpos : ∀ g, 0 < ρ g)
    (hscale : ∀ g : G, ρ g • μ.map (fun x => g * x) = μ) :
    (μ.withDensity (fun x => (((ρ x)⁻¹ : ℝ≥0) : ℝ≥0∞))).IsMulLeftInvariant := by
  let w : G → ℝ≥0∞ := fun x => ((ρ x)⁻¹ : ℝ≥0)
  have hw : Measurable w := measurable_coe_nnreal_ennreal.comp hρ.inv
  constructor
  intro g
  have hweight : (fun x => (ρ g : ℝ≥0∞) * w (g * x)) = w := by
    funext x
    simp only [w, map_mul, mul_inv, ENNReal.coe_mul]
    rw [← mul_assoc, ← ENNReal.coe_mul, mul_inv_cancel₀ (hpos g).ne', ENNReal.coe_one, one_mul]
  have hnorm : (ρ g : ℝ≥0∞) • μ.withDensity (w ∘ (fun x => g * x)) = μ.withDensity w := by
    rw [← withDensity_smul _ (hw.comp (measurable_const_mul g))]
    exact congrArg (Measure.withDensity μ) hweight
  have hh := congrArg (fun ν : Measure G => ν.withDensity w) (hscale g)
  change ((ρ g : ℝ≥0∞) • μ.map (fun x => g * x)).withDensity w = μ.withDensity w at hh
  rw [withDensity_smul_measure, ← map_withDensity_pullback μ _ (measurable_const_mul g) w hw,
    ← Measure.map_smul _ (measurable_const_mul g).aemeasurable] at hh
  rw [hnorm] at hh
  exact hh

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.DensityPushforward.Construction
