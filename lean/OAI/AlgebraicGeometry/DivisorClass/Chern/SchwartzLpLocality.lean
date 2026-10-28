import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.Adjoint

/-! # Schwartz Lp Locality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzLpLocality

noncomputable section

/-! A Schwartz L² pairing only sees the source on the prescribed support of its test. -/

open _root_.MeasureTheory
open scoped SchwartzMap

theorem lp_schwartz_inner_eq_on {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (q : 𝓢(E, F)) (S : Set E) (hq : ∀ x ∉ S, q x = 0)
    (a b : Lp F 2 (volume : Measure E))
    (hab : ∀ᵐ x ∂(volume : Measure E), x ∈ S → a x = b x) :
    inner ℝ a (q.toLp 2 volume) = inner ℝ b (q.toLp 2 volume) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [q.coeFn_toLp 2 volume, hab] with x hqLp hx
  by_cases hs : x ∈ S
  · rw [hx hs]
  · rw [hqLp, hq x hs, inner_zero_right, inner_zero_right]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzLpLocality
