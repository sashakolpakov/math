import OAI.Analysis.PDE.Elliptic.Boundary.FieldCalculus
import OAI.Analysis.PDE.Elliptic.Boundary.Schauder.Drift
import OAI.Analysis.PDE.Dirichlet.RealOperator

/-! Exact differentiation by a variable vector field.  Unlike a rigid-motion
commutator, this retains the curvature terms needed for a boundary chart. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.PDE.Dirichlet InnerProductSpace Filter
open scoped Topology

section Elliptic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The chart commutator only uses two derivatives of the solution. -/
def fieldCommutator (A : E → E →L[ℝ] E) (f : E → ℝ) (T : E → E) (x : E) : ℝ :=
  ∑ i, let b := stdOrthonormalBasis ℝ E i
    fderiv ℝ (fderiv ℝ f) x (A x b) (fderiv ℝ T x b) +
    fderiv ℝ (fderiv ℝ f) x b (fderiv ℝ T x (A x b)) +
    fderiv ℝ f x (fderiv ℝ (fderiv ℝ T) x (A x b) b)

theorem ellipticTrace_eq_hessian_sum (A : E → E →L[ℝ] E) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) :
    ellipticTrace A f x = ∑ i, fderiv ℝ (fderiv ℝ f) x
      (A x (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) := by
  let b := stdOrthonormalBasis ℝ E
  change LinearMap.trace ℝ E ((A x).toLinearMap * (fderiv ℝ (gradient f) x).toLinearMap) = _
  rw [LinearMap.trace_mul_comm, LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ (b i) (fderiv ℝ (gradient f) x (A x (b i))) = _
  rw [real_inner_comm, inner_fderiv_gradient_at hf]

theorem ellipticTrace_fieldDerivative (A : E → E →L[ℝ] E) {f : E → ℝ} {T : E → E}
    (hf : ContDiff ℝ 3 f) (hT : ContDiff ℝ 2 T) (x : E) :
    ellipticTrace A (fieldDerivative f T) x =
      ellipticTrace A (OAI.Analysis.PDE.Dirichlet.directionalDerivative f (T x)) x + fieldCommutator A f T x := by
  rw [ellipticTrace_eq_hessian_sum A
      (contDiff_fieldDerivative hf hT (by norm_num)).contDiffAt,
    ellipticTrace_eq_hessian_sum A
      (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hf (by norm_num : (2 : WithTop ENat) + 1 ≤ 3) (T x)).contDiffAt]
  simp only [hessian_fieldDerivative hf hT, OAI.Analysis.PDE.Dirichlet.hessian_directionalDerivative hf, fieldCommutator,
    Finset.sum_add_distrib]
  ring

end Elliptic

/-- Exact differentiated log-Moore equation, with no third derivative on
the right side. -/
theorem log_equation_fieldDerivative_eq {n : ℕ}
    {u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {T : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
    (hu : ContDiff ℝ 3 u) (hT : ContDiff ℝ 2 T) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
    (hf : DifferentiableAt ℝ f x)
    (heq : (fun y => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y))
      =ᶠ[𝓝 x] f) :
    ellipticTrace (fun y => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y))
      (fieldDerivative u T) x = fderiv ℝ f x (T x) / f x +
        fieldCommutator (fun y => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) u T x := by
  rw [ellipticTrace_fieldDerivative _ hu hT,
    OAI.Analysis.PDE.Dirichlet.logRealOperator_linearization _ (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (m := 2) (by norm_num) _),
    OAI.Analysis.PDE.Dirichlet.mooreLinearization_directional_eq hu (T x) hf heq, heq.eq_of_nhds]
  rfl

end OAI.Analysis.PDE.Elliptic
