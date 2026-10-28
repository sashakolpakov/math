import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantMeasureCoordinates
import Mathlib.MeasureTheory.Measure.Prod

/-! # Product Finite Measure -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.ProductFiniteMeasure.Construction

noncomputable section

/-! A finite-measure set in the noncompact coordinate has finite
measure after multiplication by the full compact coordinate. -/

open scoped Pointwise NNReal ENNReal
open _root_.MeasureTheory _root_.MeasureTheory.Measure Set

theorem compact_product_image_measure_lt_top
    {A P G : Type*} [Group A] [Group P] [Group G]
    [MeasurableSpace A] [MeasurableSpace P] [MeasurableSpace G] [MeasurableInv P]
    (α : A →* G) (β : P →* G) (e : A × P ≃ᵐ G)
    (he : ∀ x : A × P, e x = α x.1 * (β x.2)⁻¹)
    (μ : Measure G) (νA : Measure A) [IsFiniteMeasure νA] (νP : Measure P) [SFinite νP]
    (c : ℝ≥0) (hmap : μ.map e.symm = c • νA.prod νP)
    (S : Set P) (hS : νP.inv S < ⊤) : μ (Set.range α * (β '' S)) < ⊤ := by
  have himage : e '' (Set.univ ×ˢ S⁻¹) = Set.range α * (β '' S) := by
    ext g
    constructor
    · rintro ⟨⟨a, p⟩, ⟨_, hp⟩, rfl⟩
      refine ⟨α a, ⟨a, rfl⟩, β p⁻¹, ⟨p⁻¹, hp, rfl⟩, ?_⟩
      rw [he, map_inv]
    · rintro ⟨_, ⟨a, rfl⟩, _, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨(a, p⁻¹), ⟨Set.mem_univ _, ?_⟩, ?_⟩
      · change p⁻¹⁻¹ ∈ S
        simpa only [inv_inv] using hp
      · rw [he, map_inv, inv_inv]
  have hm : μ (Set.range α * (β '' S)) = (c : ℝ≥0∞) * (νA Set.univ * νP.inv S) := by
    calc
      μ (Set.range α * (β '' S)) = (μ.map e.symm) (Set.univ ×ˢ S⁻¹) := by
        have hpre : e.symm ⁻¹' (Set.univ ×ˢ S⁻¹) = e '' (Set.univ ×ˢ S⁻¹) :=
          (e.toEquiv.image_eq_preimage_symm _).symm
        rw [e.symm.map_apply, hpre, himage]
      _ = (c : ℝ≥0∞) * (νA Set.univ * νP.inv S) := by
        rw [hmap, Measure.smul_apply, Measure.prod_prod, Measure.inv_apply]
        rfl
  rw [hm]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top (measure_lt_top νA Set.univ) hS)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.ProductFiniteMeasure.Construction
