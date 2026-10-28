import OAI.Analysis.PDE.Elliptic.Boundary.ChainRule
import OAI.Analysis.PDE.Elliptic.HessianTrace
import OAI.Analysis.PDE.Elliptic.LinearCalculus

/-! Exact second-order chain rule in the real Hessian-operator form. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem inner_fderiv_gradient_at {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    inner ℝ (fderiv ℝ (gradient f) x v) w = fderiv ℝ (fderiv ℝ f) x v w := by
  have hd : fderiv ℝ (gradient f) x =
      (toDual ℝ E).symm.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) x) := by
    exact ((toDual ℝ E).symm.hasFDerivAt.comp x
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt).fderiv
  rw [hd]
  change ((toDual ℝ E) ((toDual ℝ E).symm (fderiv ℝ (fderiv ℝ f) x v))) w = _
  rw [LinearIsometryEquiv.apply_symm_apply]

omit [FiniteDimensional ℝ E] in
theorem second_fderiv_linear_comp (L : E →L[ℝ] ℝ) {g : E → E} {x : E}
    (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => L (g y))) x v w = L (fderiv ℝ (fderiv ℝ g) x v w) := by
  have hL : fderiv ℝ (L : E → ℝ) = fun _ => L := funext (fun _ => L.fderiv)
  have hz : fderiv ℝ (fun _ : E => L) (g x) = 0 := by
    simp
  simpa only [hL, hz, zero_apply, zero_add] using!
    second_fderiv_comp L.contDiff.contDiffAt hg v w

theorem hessianOperator_comp {u : E → ℝ} {g : E → E} {x : E}
    (hu : ContDiffAt ℝ 2 u (g x)) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (gradient (fun y => u (g y))) x =
      (fderiv ℝ g x).adjoint.comp ((fderiv ℝ (gradient u) (g x)).comp (fderiv ℝ g x)) +
      fderiv ℝ (gradient (fun y => fderiv ℝ u (g x) (g y))) x := by
  have hcomp : ContDiffAt ℝ 2 (fun y => u (g y)) x := hu.comp x hg
  have hlin : ContDiffAt ℝ 2 (fun y => fderiv ℝ u (g x) (g y)) x :=
    (fderiv ℝ u (g x)).contDiff.contDiffAt.comp x hg
  ext v
  apply ext_inner_right ℝ
  intro w
  simp only [add_apply, ContinuousLinearMap.comp_apply, inner_add_left]
  rw [inner_fderiv_gradient_at hcomp,
    ContinuousLinearMap.adjoint_inner_left, inner_fderiv_gradient_at hu,
    inner_fderiv_gradient_at hlin,
    second_fderiv_linear_comp _ hg]
  exact second_fderiv_comp hu hg v w

/-- The principal part transforms by Jacobian congruence; the remaining
term is exactly the old operator applied to the frozen differential of u
acting on the coordinate map. -/
theorem ellipticTrace_comp (A : E → E →L[ℝ] E) {u : E → ℝ} {g : E → E} {x : E}
    (hu : ContDiffAt ℝ 2 u (g x)) (hg : ContDiffAt ℝ 2 g x) :
    ellipticTrace A (fun y => u (g y)) x =
      ellipticTrace (fun _ => pullbackEllipticOperator (fderiv ℝ g x) (A x)) u (g x) +
      ellipticTrace A (fun y => fderiv ℝ u (g x) (g y)) x := by
  unfold ellipticTrace
  rw [hessianOperator_comp hu hg, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.toLinearMap_add, map_add]
  congr 1
  let a := (A x).toLinearMap
  let t := (fderiv ℝ g x).toLinearMap
  let s := (fderiv ℝ g x).adjoint.toLinearMap
  let h := (fderiv ℝ (gradient u) (g x)).toLinearMap
  change LinearMap.trace ℝ E (a * (s * (h * t))) = LinearMap.trace ℝ E ((t * (a * s)) * h)
  simpa only [mul_assoc] using LinearMap.trace_mul_comm ℝ (a * s * h) t

end OAI.Analysis.PDE.Elliptic
