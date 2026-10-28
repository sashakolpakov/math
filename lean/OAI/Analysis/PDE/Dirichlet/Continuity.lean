import OAI.Analysis.PDE.Dirichlet.Hessian
import OAI.LinearAlgebra.Moore.Boundary

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem continuous_realHessian {n s : ℕ} {f : CoordinateSpace n s → ℝ}
    (hf : ContDiff ℝ 2 f) : Continuous (realHessian f) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ f)) := h1.fderiv_right (by norm_num)
  unfold realHessian
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (h2.continuous.clm_apply continuous_const).clm_apply continuous_const

theorem continuous_quaternionHessian {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {f : CoordinateSpace n s → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (quaternionHessian e f) := by
  have hH := continuous_realHessian hf
  unfold quaternionHessian OAI.Analysis.Calculus.Quaternion.hessianMap
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  apply continuous_finsetSum
  intro α _
  apply continuous_finsetSum
  intro β _
  exact (((continuous_apply (b, β)).comp ((continuous_apply (a, α)).comp hH))).smul continuous_const

theorem continuous_mooreHessian {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {f : CoordinateSpace n s → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (fun x ↦ OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian e f x)) :=
  (OAI.LinearAlgebra.Moore.continuous_mooreDet n).comp (continuous_quaternionHessian e hf)

theorem continuous_mooreAffineDifferential {X : Type*} [TopologicalSpace X]
    {n : ℕ} (A R : X → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : Continuous A) (hR : Continuous R) :
    Continuous (fun p : X × ℝ ↦ ‖OAI.LinearAlgebra.Moore.mooreDifferential n (A p.1 + p.2 • R p.1) (R p.1)‖) := by
  have hc : Continuous (fun p : X × ℝ ↦ (A p.1 + p.2 • R p.1, R p.1)) := by fun_prop
  exact ((OAI.LinearAlgebra.Moore.continuous_mooreDifferential n).comp
    (f := fun p : X × ℝ ↦ (A p.1 + p.2 • R p.1, R p.1)) hc).norm

end OAI.Analysis.PDE.Dirichlet
