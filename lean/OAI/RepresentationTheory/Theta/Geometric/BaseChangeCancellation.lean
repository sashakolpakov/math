import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Algebra.Rat

/-! # Base Change Cancellation -/

namespace OAI.RepresentationTheory.Theta.Geometric.BaseChangeCancellation

noncomputable section

/-! Scalar extension retains the cancellation of an actual linear
equivalence with the inverse used in a transported map. -/

theorem baseChange_equiv_cancel
    {U V W : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (q : U ≃ₗ[ℚ] V) (t : W →ₗ[ℚ] V) (v : TensorProduct ℚ ℂ W) :
    q.toLinearMap.baseChange ℂ ((q.symm.toLinearMap.comp t).baseChange ℂ v) = t.baseChange ℂ v := by
  have h : q.toLinearMap.comp (q.symm.toLinearMap.comp t) = t := by
    apply LinearMap.ext
    intro w
    exact q.apply_symm_apply (t w)
  have hc : (q.toLinearMap.baseChange ℂ).comp ((q.symm.toLinearMap.comp t).baseChange ℂ) =
      t.baseChange ℂ := by rw [← LinearMap.baseChange_comp, h]
  exact LinearMap.congr_fun hc v

end

end OAI.RepresentationTheory.Theta.Geometric.BaseChangeCancellation
