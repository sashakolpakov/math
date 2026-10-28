import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.Normed.Module.Basic

/-! # Uncountable Ball -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.UncountableBall

noncomputable section

/-! Every nonempty ball in a nontrivial real normed space is uncountable. -/

open Set _root_.Metric
open scoped _root_.Topology

theorem normed_ball_not_countable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V]
    (x : V) {r : ℝ} (hr : 0 < r) : ¬(ball x r).Countable := by
  intro hcount
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let f : ℝ → V := fun t => x + t • v
  have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hi : Function.Injective f := fun a b h =>
    smul_left_injective ℝ hv (add_left_cancel h)
  have hO : IsOpen (f ⁻¹' ball x r) := isOpen_ball.preimage hf
  have hzero : (0 : ℝ) ∈ f ⁻¹' ball x r := by
    simpa only [mem_preimage, f, zero_smul, add_zero] using mem_ball_self hr
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hO 0 hzero
  have hinterval : (Ioo (-ε) ε).Countable := by
    have h := (hcount.preimage hi).mono hsub
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using h
  have hle := Cardinal.Real.Ioo_countable_iff.mp hinterval
  linarith

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.UncountableBall
