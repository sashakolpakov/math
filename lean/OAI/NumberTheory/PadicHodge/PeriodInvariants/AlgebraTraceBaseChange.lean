import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.TensorProduct.Free

/-! # Algebra Trace Base Change -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.AlgebraTraceBaseChange

noncomputable section

/-! # Canonical algebra trace after base change -/

open scoped TensorProduct

variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A]

theorem multiplication (y : S) :
    Algebra.lmul A (A ⊗[R] S) (1 ⊗ₜ[R] y) = (Algebra.lmul R S y).baseChange A := by
  ext a
  simp [Algebra.TensorProduct.tmul_mul_tmul]

variable [Module.Free R S] [Module.Finite R S]

theorem includeRight (y : S) :
    Algebra.trace A (A ⊗[R] S) (1 ⊗ₜ[R] y) = algebraMap R A (Algebra.trace R S y) := by
  rw [Algebra.trace_apply, multiplication, LinearMap.trace_baseChange]
  rfl

theorem tmul (a : A) (y : S) :
    Algebra.trace A (A ⊗[R] S) (a ⊗ₜ[R] y) = a * algebraMap R A (Algebra.trace R S y) := by
  have h := (Algebra.trace A (A ⊗[R] S)).map_smul a (1 ⊗ₜ[R] y)
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, includeRight R S A] using h

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.AlgebraTraceBaseChange
