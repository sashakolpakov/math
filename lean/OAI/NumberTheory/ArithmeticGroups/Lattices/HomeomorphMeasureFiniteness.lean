import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Homeomorph Measure Finiteness -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.HomeomorphMeasureFiniteness.Construction

noncomputable section

/-! A homeomorphism preserves finiteness of a measure on compact sets. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem isFiniteMeasureOnCompacts_map_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (e : X ≃ₜ Y) (μ : Measure X) [IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts (μ.map e) := by
  constructor
  intro K hK
  have hmap : (μ.map e) K = μ (e ⁻¹' K) := e.toMeasurableEquiv.map_apply K
  have hpre : e ⁻¹' K = e.symm '' K := (e.toEquiv.symm.image_eq_preimage_symm K).symm
  rw [hmap, hpre]
  exact (hK.image e.symm.continuous).measure_lt_top

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.HomeomorphMeasureFiniteness.Construction
