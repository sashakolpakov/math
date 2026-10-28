import OAI.NumberTheory.PadicHodge.GeometricComparison.Linear
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Tensor Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TensorCoordinates.CoefficientCoordinates

noncomputable section

/-! A coefficient basis identifies scalar extension with a finite product naturally. -/

open scoped TensorProduct

variable {K L I V W : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def equiv (b : Module.Basis I K L) : (L ⊗[K] V) ≃ₗ[K] (I → V) :=
  (TensorProduct.comm K L V).trans
    ((TensorProduct.congr (LinearEquiv.refl K V) b.equivFun).trans
      (TensorProduct.piScalarRight K K V I))

theorem equiv_tmul (b : Module.Basis I K L) (l : L) (v : V) :
    equiv b (l ⊗ₜ[K] v) = fun i => b.equivFun l i • v := by
  simp [equiv]

theorem naturality (b : Module.Basis I K L) (f : V →ₗ[K] W) (x : L ⊗[K] V) :
    equiv b (f.baseChange L x) = fun i => f (equiv b x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul l v => simp [equiv_tmul]
  | add x y hx hy => ext i; simp [map_add, hx, hy]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TensorCoordinates.CoefficientCoordinates
