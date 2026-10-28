import OAI.Analysis.PDE.Dirichlet.MatrixBounds

open Set
open scoped ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- The interior gradient estimate, once the defining-function coercivity and
boundary gradient have been bounded. The differentiated equation is proved,
not included among the assumptions. -/
theorem quaternionic_gradient_estimate_of_barrier_coercivity {n : ℕ} (hn : 1 ≤ n)
    {K : Set (CoordinateSpace n 4)} (hK : IsCompact K)
    {ψ r F : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ 3 ψ) (hr : ContDiff ℝ 2 r)
    (hF : DifferentiableOn ℝ F (interior K))
    (hA : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (heq : ∀ x ∈ interior K, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x)
    (v : CoordinateSpace n 4) {κ L B : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L)
    (hcoercive : ∀ x ∈ interior K, κ ≤ mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) r x)
    (hdata : ∀ x ∈ interior K, |directionalDerivative F v x| ≤ L)
    (hboundary : ∀ x ∈ K, x ∉ interior K → |directionalDerivative ψ v x| ≤ B)
    (hrbd : ∀ x ∈ K, x ∉ interior K → r x = 0) :
    ∀ x ∈ K, |directionalDerivative ψ v x| ≤ B - (L / κ) * r x := by
  apply moore_linearized_barrier_estimate hn hK
    (contDiff_directionalDerivative hψ (by norm_num) v) hr hA ?_ hboundary hrbd
  intro x hx
  rw [mooreLinearization_directional_eq_on_open hψ isOpen_interior hF heq v hx]
  calc
    |directionalDerivative F v x| ≤ L := hdata x hx
    _ = (L / κ) * κ := (div_mul_cancel₀ L hκ.ne').symm
    _ ≤ (L / κ) * mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) r x :=
      mul_le_mul_of_nonneg_left (hcoercive x hx) (div_nonneg hL hκ.le)

end OAI.Analysis.PDE.Dirichlet
