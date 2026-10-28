import OAI.Analysis.PDE.Concentration.NullGradient
import OAI.Analysis.PDE.Green.Physical.BoundaryTransfer

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Green
open scoped Matrix

theorem physicalFullDefining_eq_null (d : ℕ) (a : ℝ) :
    OAI.Analysis.PDE.Green.physicalFullDefining d a =
      fun x => OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a (physicalToNullCurrentPoint d x).2 := by
  funext x
  rw [physicalToNullCurrentPoint_imaginary]
  rfl

theorem physicalFullDefining_hessian (d : ℕ) (a : ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (hx : (physicalToNullCurrentPoint d x).2 none ≠ 0) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (OAI.Analysis.PDE.Green.physicalFullDefining d a) x =
      physicalMatrix (OAI.Analysis.Calculus.Current.fiberHessian (1 / 10) a (physicalToNullCurrentPoint d x).2) := by
  rw [physicalFullDefining_eq_null]
  have hU : IsOpen {z : OAI.Analysis.Calculus.Current.Index d → ℂ | z none ≠ 0} :=
    isOpen_ne.preimage (continuous_apply none)
  have hf : ContDiffOn ℝ 2 (OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a) {z : OAI.Analysis.Calculus.Current.Index d → ℂ | z none ≠ 0} := by
    intro z hz
    exact ((OAI.Analysis.Calculus.Current.contDiffAt_fiberDefining (1 / 10) a z hz).of_le (by norm_num)).contDiffWithinAt
  exact quaternionHessian_physical_null hU hf x hx

theorem physicalFullDefining_gradient (d : ℕ) (a : ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (hx : (physicalToNullCurrentPoint d x).2 none ≠ 0) :
    OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots (OAI.Analysis.PDE.Green.physicalFullDefining d a) x =
      physicalVector (OAI.Analysis.Calculus.Current.fiberGradient (1 / 10) a (physicalToNullCurrentPoint d x).2) := by
  rw [physicalFullDefining_eq_null]
  exact quaternionGradient_physical_null x
    ((OAI.Analysis.Calculus.Current.contDiffAt_fiberDefining (1 / 10) a _ hx).differentiableAt (by norm_num))

/-- The actual physical defining function and actual background have a common
nonzero Hessian null direction tangent to the defining function. -/
theorem physicalFullDefining_common_kernel (d : ℕ) (a : ℝ) (ha : a ≠ 0)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : (physicalToNullCurrentPoint d x).2 none ≠ 0) :
    ∃ w : Fin (d + 2) → Quaternion ℝ, w ≠ 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (OAI.Analysis.PDE.Green.physicalFullDefining d a) x *ᵥ w = 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (physicalBackground d) x *ᵥ w = 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots (OAI.Analysis.PDE.Green.physicalFullDefining d a) x) ⬝ᵥ w = 0 := by
  let z := (physicalToNullCurrentPoint d x).2
  let v : OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ := fun b => OAI.Analysis.Calculus.Current.complexK (OAI.Analysis.Calculus.Current.fiberKernelVector z b)
  have hv : v ≠ 0 := by
    intro he
    have hn := congrFun he none
    norm_num [v, OAI.Analysis.Calculus.Current.fiberKernelVector, OAI.Analysis.Calculus.Current.complexK] at hn
    have hr := congrArg (fun q : Quaternion ℝ => q.re) hn
    norm_num at hr
  have hH : OAI.Analysis.Calculus.Current.fiberHessian (1 / 10) a z *ᵥ v = 0 := OAI.Analysis.Calculus.Current.fiberHessian_kernel _ _ _ hx
  refine ⟨physicalVector v, ?_, ?_, ?_, ?_⟩
  · intro he
    exact hv ((physicalVector_injective d) (he.trans (physicalVector_zero d).symm))
  · rw [physicalFullDefining_hessian d a x hx, physicalMatrix_mulVec, hH, physicalVector_zero]
  · rw [physicalBackground_hessian d x hx, physicalMatrix_mulVec,
      OAI.Analysis.Calculus.Current.fiberHessian_kernel_background (1 / 10) a z v ha hx hH, physicalVector_zero]
  · rw [physicalFullDefining_gradient d a x hx, physicalVector_dot]
    exact OAI.Analysis.Calculus.Current.fiberHessian_kernel_orthogonal_gradient (1 / 10) a z hx v hH

end OAI.Analysis.PDE.Concentration
