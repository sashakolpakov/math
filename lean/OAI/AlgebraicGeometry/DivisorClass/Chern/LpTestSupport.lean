import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.Support

/-! # Lp Test Support -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.LpTestSupport

noncomputable section

/-! L² pairings depend only on the source values on the support of the fixed test. -/

open _root_.MeasureTheory

theorem memLp_real_inner_eq_on_test_support
    {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {μ : Measure X} (a b q : X → F) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) (hq : MemLp q 2 μ)
    (heq : ∀ x ∈ Function.support q, a x = b x) :
    inner ℝ (ha.toLp a) (hq.toLp q) = inner ℝ (hb.toLp b) (hq.toLp q) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  apply Filter.Eventually.mono (ha.coeFn_toLp.and (hb.coeFn_toLp.and hq.coeFn_toLp))
  intro x hx
  dsimp only
  rw [hx.1, hx.2.1, hx.2.2]
  by_cases hqzero : q x = 0
  · simp only [hqzero, inner_zero_right]
  · exact congrArg (fun v => inner ℝ v (q x)) (heq x hqzero)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.LpTestSupport
