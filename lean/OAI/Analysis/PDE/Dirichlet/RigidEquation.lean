import OAI.Analysis.PDE.Dirichlet.Covariance

open Filter Set
open scoped Matrix Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem complexify_trace_eq_zero_of_skew {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (hA : Aᴴ = -A) : (OAI.LinearAlgebra.Moore.complexify A).trace.re = 0 := by
  have hdiag (i : Fin n) : (A i i).re = 0 := by
    have h := congrArg (fun B : Matrix (Fin n) (Fin n) Q ↦ (B i i).re) hA
    simp at h
    linarith
  rw [OAI.LinearAlgebra.Moore.complexify_trace_real]
  simp only [hdiag, Finset.sum_const_zero, mul_zero]

/-- Infinitesimal unitary invariance of the signed Moore polynomial, even at
singular or indefinite matrices. -/
theorem mooreDifferential_skew_congruence {n : ℕ} (H A : Matrix (Fin n) (Fin n) Q)
    (hA : Aᴴ = -A) : OAI.LinearAlgebra.Moore.mooreDifferential n H (Aᴴ * H + H * A) = 0 := by
  have hAt : (Aᴴ)ᴴ = -(Aᴴ) := by
    rw [Matrix.conjTranspose_conjTranspose, hA, neg_neg]
  have h := OAI.LinearAlgebra.Moore.mooreDifferential_congruence n H Aᴴ
  rw [complexify_trace_eq_zero_of_skew Aᴴ hAt] at h
  simpa only [Matrix.conjTranspose_conjTranspose, zero_mul] using h

/-- The rigid-motion differentiated equation from the mixed boundary estimate.
The commutator vanishes by the proved covariance and polynomial invariance;
it is not assumed as a property of an abstract elliptic operator. -/
theorem mooreLinearization_rigid_eq {n : ℕ} {ψ F : CoordinateSpace n 4 → ℝ}
    (hψ : ContDiff ℝ 3 ψ) (e : CoordinateSpace n 4) (A : Matrix (Fin n) (Fin n) Q)
    (hA : Aᴴ = -A) {x : CoordinateSpace n 4} (hF : DifferentiableAt ℝ F x)
    (heq : (fun y ↦ OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y)) =ᶠ[𝓝 x] F) :
    mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ)
        (affineDerivative ψ e (realMatrixAction (realRepresentation A))) x =
      affineDerivative F e (realMatrixAction (realRepresentation A)) x := by
  have hc : OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)
      (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x * A + Aᴴ * quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = 0 := by
    simpa only [add_comm] using mooreDifferential_skew_congruence (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) A hA
  unfold mooreLinearization
  rw [quaternionHessian_affineDerivative hψ, add_assoc, OAI.LinearAlgebra.Moore.mooreDifferential_add, hc, add_zero]
  exact mooreLinearization_directional_eq hψ
    (e + realMatrixAction (realRepresentation A) x) hF heq

theorem mooreLinearization_rigid_eq_on_open {n : ℕ} {ψ F : CoordinateSpace n 4 → ℝ}
    (hψ : ContDiff ℝ 3 ψ) {Ω : Set (CoordinateSpace n 4)} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℝ F Ω)
    (heq : ∀ x ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x)
    (e : CoordinateSpace n 4) (A : Matrix (Fin n) (Fin n) Q) (hA : Aᴴ = -A)
    {x : CoordinateSpace n 4} (hx : x ∈ Ω) :
    mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ)
        (affineDerivative ψ e (realMatrixAction (realRepresentation A))) x =
      affineDerivative F e (realMatrixAction (realRepresentation A)) x := by
  apply mooreLinearization_rigid_eq hψ e A hA ((hF x hx).differentiableAt (hΩ.mem_nhds hx))
  filter_upwards [hΩ.mem_nhds hx] with y hy
  exact heq y hy

end OAI.Analysis.PDE.Dirichlet
