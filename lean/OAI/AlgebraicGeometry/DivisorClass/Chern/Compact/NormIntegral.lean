import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Norm Integral -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.NormIntegral

/-! Squared norms of continuous compactly supported fields are integrable. -/

open _root_.MeasureTheory

variable {X F : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup F] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

theorem compact_norm_sq_integrable (f : X → F) (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun x => ‖f x‖ ^ 2) μ := by
  have hzero : ‖(0 : F)‖ ^ 2 = 0 := by rw [norm_zero, zero_pow (by decide : 2 ≠ 0)]
  have hs : HasCompactSupport (fun x => ‖f x‖ ^ 2) := hc.comp_left (g := fun v : F => ‖v‖ ^ 2) hzero
  exact (hf.norm.pow 2).integrable_of_hasCompactSupport hs

end OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.NormIntegral
