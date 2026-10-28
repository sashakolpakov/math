import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantMeasureCoordinates
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Haar From Homeomorphic Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.HaarFromHomeomorphicCoordinates.Construction

noncomputable section

/-! A homeomorphic coordinate chart carrying a measure finite on
compact sets, positive on open sets, and invariant under translations
pushes that measure to Haar measure on the group. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem isHaarMeasure_of_homeomorphic_coordinates
    {X G : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (e : X ≃ₜ G) (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [IsOpenPosMeasure μ]
    (τ : G → X → X) (hτ : ∀ g, MeasurePreserving (τ g) μ μ)
    (he : ∀ g x, e (τ g x) = g * e x) : IsHaarMeasure (μ.map e) := by
  have hleft : IsMulLeftInvariant (μ.map e) := by
    apply InvariantMeasureCoordinates.Construction.isMulLeftInvariant_map_inverse_of_equivariant e.symm.toMeasurableEquiv μ τ hτ
    intro g h
    apply e.injective
    change e (e.symm (g * h)) = e (τ g (e.symm h))
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  have hpos : IsOpenPosMeasure (μ.map e) := e.continuous.isOpenPosMeasure_map e.surjective
  refine
    { toIsMulLeftInvariant := hleft
      toIsOpenPosMeasure := hpos
      lt_top_of_isCompact := ?_ }
  intro K hK
  have hmap : (μ.map e) K = μ (e ⁻¹' K) := e.toMeasurableEquiv.map_apply K
  rw [hmap]
  have hpre : e ⁻¹' K = e.symm '' K := (e.toEquiv.symm.image_eq_preimage_symm K).symm
  rw [hpre]
  exact (hK.image e.symm.continuous).measure_lt_top

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.HaarFromHomeomorphicCoordinates.Construction
