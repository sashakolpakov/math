import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantMeasureCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.FactorHaarInvariance

/-! # Product Haar Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.ProductHaarCoordinates.Construction

noncomputable section

/-! In compact/closed product coordinates, with the second coordinate
inverted, right Haar measure is a scalar multiple of product left Haar measure. -/

open scoped NNReal
open _root_.MeasureTheory _root_.MeasureTheory.Measure Set

theorem inverseHaar_compact_product_coordinates
    {A P G : Type*} [Group A] [Group P] [Group G]
    [TopologicalSpace A] [TopologicalSpace P] [TopologicalSpace G]
    [IsTopologicalGroup A] [IsTopologicalGroup P] [IsTopologicalGroup G]
    [T2Space A] [T2Space P] [T2Space G] [CompactSpace A]
    [LocallyCompactSpace P] [LocallyCompactSpace G]
    [SecondCountableTopology A] [SecondCountableTopology P] [SecondCountableTopology G]
    [MeasurableSpace A] [MeasurableSpace P] [MeasurableSpace G]
    [BorelSpace A] [BorelSpace P] [BorelSpace G]
    (α : A →* G) (β : P →* G) (hα : Continuous α)
    (e : A × P ≃ₜ G) (he : ∀ x : A × P, e x = α x.1 * (β x.2)⁻¹)
    (μ : Measure G) [IsHaarMeasure μ] (νA : Measure A) [IsHaarMeasure νA]
    (νP : Measure P) [IsHaarMeasure νP] :
    ∃ c : ℝ≥0, μ.inv.map e.symm = c • νA.prod νP := by
  have hK : IsCompact (α.range : Set G) := by
    simpa only [MonoidHom.coe_range, Set.image_univ] using isCompact_univ.image hα
  let τ : A × P → G → G := fun x g => α x.1 * g * (β x.2)⁻¹
  have hτ (x : A × P) : MeasurePreserving (τ x) μ.inv μ.inv :=
    (measurePreserving_mul_right μ.inv (β x.2)⁻¹).comp
      (FactorHaarInvariance.Construction.inverseHaar_left_compact_subgroup_invariant μ α.range hK (α x.1) ⟨x.1, rfl⟩)
  have heq (x y : A × P) : e (x * y) = τ x (e y) := by
    rw [he, he]
    change α (x.1 * y.1) * (β (x.2 * y.2))⁻¹ = α x.1 * (α y.1 * (β y.2)⁻¹) * (β x.2)⁻¹
    rw [map_mul, map_mul, mul_inv_rev]
    simp only [mul_assoc]
  let ρ := μ.inv.map e.symm
  let : IsMulLeftInvariant ρ := InvariantMeasureCoordinates.Construction.isMulLeftInvariant_map_inverse_of_equivariant e.toMeasurableEquiv μ.inv τ hτ heq
  let : IsFiniteMeasureOnCompacts ρ := IsFiniteMeasureOnCompacts.map μ.inv e.symm
  exact ⟨haarScalarFactor ρ (νA.prod νP), isMulLeftInvariant_eq_smul ρ (νA.prod νP)⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.ProductHaarCoordinates.Construction
