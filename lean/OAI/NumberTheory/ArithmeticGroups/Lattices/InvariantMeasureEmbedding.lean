import OAI.NumberTheory.ArithmeticGroups.Lattices.QuotientMeasure
import Mathlib.MeasureTheory.Measure.Comap

/-! # Invariant Measure Embedding -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantMeasureEmbedding.Construction

noncomputable section

/-! An equivariant measurable embedding pulls an invariant measure
back to an invariant measure on its source. -/

open _root_.MeasureTheory Set

theorem equivariant_image_preimage_smul
    {G H X Y : Type*} [Group G] [Group H] [MulAction G X] [MulAction H Y]
    (f : G →* H) (p : X → Y) (hp : ∀ g x, p (g • x) = f g • p x)
    (g : G) (s : Set X) : p '' ((g • ·) ⁻¹' s) = (f g • ·) ⁻¹' (p '' s) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g • x, hx, hp g x⟩
  · rintro ⟨x, hx, he⟩
    refine ⟨g⁻¹ • x, ?_, ?_⟩
    · change g • (g⁻¹ • x) ∈ s
      simpa only [smul_inv_smul] using hx
    · rw [hp, he, map_inv, inv_smul_smul]

theorem invariant_measure_comap_embedding
    {G H X Y : Type*} [Group G] [Group H] [MulAction G X] [MulAction H Y]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableConstSMul G X]
    (f : G →* H) (p : X → Y) (hp : MeasurableEmbedding p)
    (he : ∀ g x, p (g • x) = f g • p x)
    (μ : Measure Y) [SMulInvariantMeasure H Y μ] :
    SMulInvariantMeasure G X (μ.comap p) := by
  constructor
  intro g s hs
  rw [Measure.comap_apply p hp.injective hp.measurableSet_image' μ
      (hs.preimage (measurable_const_smul g)),
    Measure.comap_apply p hp.injective hp.measurableSet_image' μ hs,
    equivariant_image_preimage_smul f p he]
  exact SMulInvariantMeasure.measure_preimage_smul (f g) (hp.measurableSet_image' hs)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantMeasureEmbedding.Construction
