import OAI.Geometry.ComplexTorus.RiemannProjectivity.DenseFiber
import OAI.Geometry.ComplexTorus.RiemannProjectivity.CoefficientRoot

/-! # Parameter Equations On -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.ParameterEquationsOn.Constructions.ParameterEquations

noncomputable section

/-! # RiemannProjectivity: extending equations from generic fibers on a holomorphic parametrization -/

open Set _root_.Polynomial
open scoped BigOperators

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem differentiableOn_eval {P : W → ℂ[X]} (k : ℕ)
    (hdegree : ∀ y, (P y).natDegree ≤ k) {O : Set W}
    (hcoeff : ∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) O)
    {F : V → W} {g : V → ℂ} {U : Set V} (hF : DifferentiableOn ℂ F U)
    (hg : DifferentiableOn ℂ g U) (hmap : MapsTo F U O) :
    DifferentiableOn ℂ (fun x => (P (F x)).eval (g x)) U := by
  have heq : (fun x => (P (F x)).eval (g x)) =
      fun x => ∑ j ∈ Finset.range (k + 1), (P (F x)).coeff j * (g x) ^ j := by
    funext x
    exact eval_eq_sum_range' (Nat.lt_succ_of_le (hdegree (F x))) (g x)
  rw [heq]
  exact DifferentiableOn.fun_sum (fun j _ => ((hcoeff j).comp hF hmap).fun_mul (hg.fun_pow j))

theorem vanishes_on_parameters {P : W → ℂ[X]} (k : ℕ)
    (hdegree : ∀ y, (P y).natDegree ≤ k) {O : Set W}
    (hcoeff : ∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) O)
    {F : V → W} {g : V → ℂ} {U : Set V} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hg : DifferentiableOn ℂ g U) (hmap : MapsTo F U O)
    (hdim : Module.finrank ℂ V = Module.finrank ℂ W)
    (hfinite : ∀ y, {z : V | z ∈ U ∧ F z = y}.Finite)
    {D : Set W} (hD : ∀ x ∈ U, F x ∈ closure D)
    (hzero : ∀ x ∈ U, F x ∈ D → (P (F x)).eval (g x) = 0) :
    ∀ x ∈ U, (P (F x)).eval (g x) = 0 := by
  have hc := (differentiableOn_eval k hdegree hcoeff hF hg hmap).continuousOn
  have hdense := DenseFiber.Constructions.DenseFiberPreimage.dense_preimage hU hF hdim hfinite hD
  intro x hx
  have hmem : (P (F x)).eval (g x) ∈ closure ({0} : Set ℂ) :=
    ((hc x hx).mono inter_subset_left).mem_closure (hdense hx)
      (fun y hy => hzero y hy.1 hy.2)
  simpa only [closure_singleton, mem_singleton_iff] using hmem

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.ParameterEquationsOn.Constructions.ParameterEquations
