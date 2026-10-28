import OAI.NumberTheory.ArithmeticGroups.Lattices.SubgroupRelativeEquiv
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.ProductHaarCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.ProductFiniteMeasure

/-! # Compact Factor Finite Volume -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CompactFactorFiniteVolume.Construction

noncomputable section

/-! Finite right Haar volume survives multiplication by a compact
factor inside a closed ambient subgroup. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure
open scoped Pointwise

theorem relative_compact_factor_inverseHaar_lt_top
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (H K P : Subgroup G) (hH : IsClosed (H : Set G))
    (hK : IsCompact (K : Set G)) (hP : IsClosed (P : Set G))
    (hKH : K ≤ H) (hPH : P ≤ H) (hKP : K ⊓ P = ⊥)
    (hcover : ∀ g ∈ H, ∃ k ∈ K, ∃ p ∈ P, k * p = g)
    (μ : Measure H) [IsHaarMeasure μ] (ν : Measure P) [IsHaarMeasure ν]
    (S : Set P) (hS : ν.inv S < ⊤) :
    μ.inv (Set.range (Subgroup.inclusion hKH) * (Subgroup.inclusion hPH '' S)) < ⊤ := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : LocallyCompactSpace P := hP.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : SecondCountableTopology H := hH.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  let : SecondCountableTopology K := hK.isClosed.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  let : SecondCountableTopology P := hP.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  let f : (K.comap H.subtype) × (P.comap H.subtype) → H := fun x => x.1.val * x.2.val
  let e₀ := (RelativeSubgroupProductCoordinates.Construction.relative_compact_closed_product_isHomeomorph H K P hH hK hP hKH hPH hKP hcover).homeomorph f
  let e₁ : K × P ≃ₜ H :=
    ((SubgroupRelativeEquiv.Construction.subgroupRelativeEquiv H K hKH).toHomeomorph.prodCongr
      (SubgroupRelativeEquiv.Construction.subgroupRelativeEquiv H P hPH).toHomeomorph).trans e₀
  let e : K × P ≃ₜ H := ((Homeomorph.refl K).prodCongr (Homeomorph.inv P)).trans e₁
  have he : ∀ x : K × P,
      e x = Subgroup.inclusion hKH x.1 * (Subgroup.inclusion hPH x.2)⁻¹ := fun _ => rfl
  have hα : Continuous (Subgroup.inclusion hKH) := continuous_subtype_val.subtype_mk _
  let νK := haar (G := K)
  obtain ⟨c, hc⟩ := Compact.ProductHaarCoordinates.Construction.inverseHaar_compact_product_coordinates (Subgroup.inclusion hKH)
    (Subgroup.inclusion hPH) hα e he μ νK ν
  exact Compact.ProductFiniteMeasure.Construction.compact_product_image_measure_lt_top (Subgroup.inclusion hKH) (Subgroup.inclusion hPH)
    e.toMeasurableEquiv he μ.inv νK ν c hc S hS

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CompactFactorFiniteVolume.Construction
