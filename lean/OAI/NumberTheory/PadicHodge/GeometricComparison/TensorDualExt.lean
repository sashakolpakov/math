import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.Tactic

/-! # Tensor Dual Ext -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TensorDualExt.DualBaseChange

noncomputable section

/-! Functionals on a scalar extension are determined by the original vectors. -/

open scoped TensorProduct

variable {R S V W : Type*} [Field R] [Field S] [Algebra R S]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]

theorem ext_via_tensor (e : (S ⊗[R] V) ≃ₗ[S] W) (f g : Module.Dual S W)
    (h : ∀ v, f (e (1 ⊗ₜ[R] v)) = g (e (1 ⊗ₜ[R] v))) : f = g := by
  apply LinearMap.ext
  intro w
  obtain ⟨x, rfl⟩ := e.surjective w
  induction x using TensorProduct.inductionOn with
  | tmul s v =>
      have hs : s ⊗ₜ[R] v = s • ((1 : S) ⊗ₜ[R] v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hs, e.map_smul, f.map_smul, g.map_smul, h v]
  | add x y hx hy => simp only [map_add, hx, hy]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TensorDualExt.DualBaseChange
