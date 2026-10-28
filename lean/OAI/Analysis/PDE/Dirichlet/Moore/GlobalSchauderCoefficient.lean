import OAI.Analysis.PDE.Dirichlet.Periodic.CoefficientMooreSmooth
import OAI.Analysis.Normed.Function.Holder.C2HolderEquationLimit

/-! The concrete Moore coefficients and the actual C²-jet equation satisfy
the coefficient and equation hypotheses of the global Schauder estimate. -/

open Set Module InnerProductSpace
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

theorem inner_operator_upper_of_norm_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) {M : ℝ} (hA : ‖A‖ ≤ M) (v : E) :
    inner ℝ v (A v) ≤ M * ‖v‖ ^ 2 := by
  calc
    inner ℝ v (A v) ≤ |inner ℝ v (A v)| := le_abs_self _
    _ ≤ ‖v‖ * ‖A v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖ * (M * ‖v‖) := mul_le_mul_of_nonneg_left
      ((A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg v)))
      (norm_nonneg v)
    _ = M * ‖v‖ ^ 2 := by ring

theorem continuous_moore_schauder_coefficient {n : ℕ}
    {ψ : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    Continuous (fun x => detRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)) :=
  (contDiff_detRealOperator n 0).continuous.comp
    (continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots hψ)

theorem moore_schauder_coefficient_symmetric {n : ℕ}
    (ψ : CoordinateSpace n 4 → ℝ) (x : CoordinateSpace n 4) :
    (detRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).toLinearMap.IsSymmetric :=
  detRealOperator_isSymmetric _

theorem moore_schauder_coefficient_quadratic_bounds {n : ℕ}
    (ψ : CoordinateSpace n 4 → ℝ) {D : Set (CoordinateSpace n 4)} {lam M : ℝ}
    (hlower : ∀ x ∈ D, ∀ v : CoordinateSpace n 4,
      lam * ‖v‖ ^ 2 ≤ inner ℝ v
        (detRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v))
    (hupper : ∀ x ∈ D, ‖detRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)‖ ≤ M) :
    ∀ x ∈ D, ∀ v : CoordinateSpace n 4,
      lam * ‖v‖ ^ 2 ≤ inner ℝ v
        (detRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v) ∧
      inner ℝ v (detRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v) ≤ M * ‖v‖ ^ 2 := by
  intro x hx v
  exact ⟨hlower x hx v, inner_operator_upper_of_norm_le _ (hupper x hx) v⟩

theorem ellipticTrace_eq_of_moore_jet_equation {n : ℕ}
    {Ω D : Set (CoordinateSpace n 4)} {hΩD : Ω ⊆ D} {α : ℝ}
    (A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) Q)
    (u : CoordinateSpace n 4 → ℝ) (hu : ContDiff ℝ 2 u)
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hU2 : ∀ x : D, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x)
    (F : CoordinateSpace n 4 → ℝ)
    (heq : ∀ x : D, OAI.LinearAlgebra.Moore.mooreDifferential n (A x)
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots U) x) = F x) :
    ∀ x ∈ D, OAI.Analysis.PDE.Elliptic.ellipticTrace (fun y => detRealOperator (A y)) u x = F x := by
  intro x hx
  rw [detRealOperator_linearization A hu x]
  have h := heq ⟨x, hx⟩
  rw [quaternionHessianField_eq_of_secondDerivative_eq OAI.Analysis.Calculus.Quaternion.fourSlots U u ⟨x, hx⟩
    (hU2 ⟨x, hx⟩)] at h
  exact h

end OAI.Analysis.PDE.Dirichlet
