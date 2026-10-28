import OAI.Analysis.Calculus.Quaternion.DirectionalHessian
import OAI.LinearAlgebra.Moore.NullLagrangian

/-! The unconditional divergence identity for the actual Moore cofactor of a
quaternionic Hessian. No definiteness or nonsingularity hypothesis is used. -/

noncomputable section
namespace OAI.Analysis.Calculus.Quaternion

open OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix Matrix.Norms.Elementwise

theorem mooreCofactor_directionalHessian_divergence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {s : Type*} [Fintype s] [DecidableEq s]
    (e : s → Q) (d : Fin n × s → E) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 3 f x) (b : Fin n) :
    strongDivergence e
      (fun p => fderiv ℝ (fun y => OAI.LinearAlgebra.Moore.mooreCofactor n (directionalHessian e d f y)) x (d p))
      b = 0 := by
  apply directionalHessian_conservation e d hf (OAI.LinearAlgebra.Moore.mooreCofactor n)
  · exact (OAI.LinearAlgebra.Moore.contDiff_mooreCofactor n 1).differentiable (by norm_num) _
  · intro g
    exact OAI.LinearAlgebra.Moore.mooreCofactor_fderiv_outer_vecMul _ g

/-- Proposition (cofactor-divergence): the Moore cofactor of a `C³` real
function's quaternionic Hessian has zero strong quaternionic divergence.
The slots may be either the manuscript's three-slot or four-slot system. -/
theorem mooreCofactor_quaternionHessian_divergence
    {n s : ℕ} (e : Fin s → Q) {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s} (hf : ContDiffAt ℝ 3 f x) (b : Fin n) :
    strongDivergence e
      (fun p => fderiv ℝ (fun y => OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e f y)) x
        (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) b = 0 :=
  mooreCofactor_directionalHessian_divergence e OAI.Analysis.PDE.Dirichlet.coordinateVector hf b

end OAI.Analysis.Calculus.Quaternion
