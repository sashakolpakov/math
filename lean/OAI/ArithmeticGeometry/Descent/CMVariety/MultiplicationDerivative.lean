import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Multiplication Derivative -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.MultiplicationDerivative.Abelian

noncomputable section

/-!
The derivative of a jointly smooth multiplication in its last variable
depends continuously on the base and the first input.
-/

open Set
open scoped _root_.Topology ContDiff

variable {P V : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem continuousOn_parameter_derivative
    (f : P × V → V) (D : Set (P × V)) (hD : IsOpen D) (hf : ContDiffOn ℝ 2 f D) :
    ContinuousOn (fun p : P => fderiv ℝ (fun v => f (p, v)) 0) {p | (p, (0 : V)) ∈ D} := by
  intro p hp
  have h : ContDiffAt ℝ 2 (Function.uncurry (fun p v => f (p, v))) (p, 0) :=
    hf.contDiffAt (hD.mem_nhds hp)
  exact (h.fderiv (g := fun _ => (0 : V)) contDiffAt_const
    (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).continuousAt.continuousWithinAt

theorem continuousOn_multiplication_derivative
    (m : P × (V × V) → V) (D : Set (P × (V × V)))
    (hD : IsOpen D) (hm : ContDiffOn ℝ 2 m D) :
    ContinuousOn (fun q : P × V => fderiv ℝ (fun y => m (q.1, (q.2, y))) 0)
      {q | (q.1, (q.2, (0 : V))) ∈ D} := by
  intro q hq
  let f : (P × V) → V → V := fun z y => m (z.1, (z.2, y))
  have hcoord : ContDiffAt ℝ 2 (fun z : (P × V) × V => (z.1.1, (z.1.2, z.2))) (q, 0) := by
    fun_prop
  have hf : ContDiffAt ℝ 2 (Function.uncurry f) (q, 0) :=
    (hm.contDiffAt (hD.mem_nhds hq)).comp (q, 0) hcoord
  exact (hf.fderiv (g := fun _ => (0 : V)) contDiffAt_const (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).continuousAt.continuousWithinAt

end

end OAI.ArithmeticGeometry.Descent.CMVariety.MultiplicationDerivative.Abelian
