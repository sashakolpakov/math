import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceDuality
import Mathlib.LinearAlgebra.Contraction

/-! # Line Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.LineTrace

noncomputable section

/-! Finite étale duality with a genuine coefficient line (or module).
The tensor extension of the algebra trace is exactly evaluation at one. -/

open scoped TensorProduct

universe u
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Free A B] [Module.Finite A B] [Algebra.Etale A B]
  (L : Type u) [AddCommGroup L] [Module A L]

def equiv : B ⊗[A] L ≃ₗ[A] (B →ₗ[A] L) :=
  (TensorProduct.congr (TraceDuality.equiv A B) (LinearEquiv.refl A L)).trans
    (dualTensorHomEquiv A B L)

theorem equiv_tmul (b x : B) (l : L) :
    equiv A B L (b ⊗ₜ[A] l) x = Algebra.trace A B (b * x) • l := rfl

def trace : B ⊗[A] L →ₗ[A] L :=
  (TensorProduct.lid A L).toLinearMap.comp ((Algebra.trace A B).rTensor L)

omit [Module.Free A B] [Module.Finite A B] [Algebra.Etale A B] in
theorem trace_tmul (b : B) (l : L) :
    LineTrace.trace A B L (b ⊗ₜ[A] l) = Algebra.trace A B b • l := rfl

theorem trace_eq_eval_one (x : B ⊗[A] L) : LineTrace.trace A B L x = equiv A B L x 1 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul b l => rw [trace_tmul, equiv_tmul, mul_one]

theorem trace_symm (f : B →ₗ[A] L) :
    LineTrace.trace A B L ((equiv A B L).symm f) = f 1 := by
  rw [trace_eq_eval_one, LinearEquiv.apply_symm_apply]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.LineTrace
