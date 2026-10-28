import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SectionTrace
import OAI.NumberTheory.PadicHodge.PeriodInvariants.TraceDualBaseChange

/-! # Fiber Section Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FiberSectionTrace

noncomputable section

/-! A point of a finite étale algebra over a quotient of the base
selects a unique trace-dual component in the actual fiber algebra.
Every lift of that component has the exact residue-evaluation trace. -/
open scoped TensorProduct
universe u
variable (B C k : Type u) [CommRing B] [CommRing C] [CommRing k]
  [Algebra B C] [Algebra B k] [Module.Free B C] [Module.Finite B C]
  [Algebra.Etale B C] (ε : C →ₐ[B] k)

def evaluation : k ⊗[B] C →ₐ[k] k := AlgHom.liftEquiv B k C k ε

omit [Module.Free B C] [Module.Finite B C] [Algebra.Etale B C] in
theorem evaluation_tmul (a : k) (x : C) : evaluation B C k ε (a ⊗ₜ[B] x) = a * ε x := rfl

def component : k ⊗[B] C :=
  SectionTrace.component k (k ⊗[B] C) (evaluation B C k ε)

omit [Module.Free B C] [Module.Finite B C] in
theorem component_evaluation : evaluation B C k ε (component B C k ε) = 1 :=
  SectionTrace.component_evaluation k (k ⊗[B] C) (evaluation B C k ε)

theorem trace_component_mul (x : C) :
    Algebra.trace k (k ⊗[B] C) (component B C k ε * (1 ⊗ₜ[B] x)) = ε x := by
  have h := SectionTrace.trace_mul k (k ⊗[B] C) (evaluation B C k ε)
    (component B C k ε) (component_evaluation B C k ε)
    (SectionTrace.component_annihilates k (k ⊗[B] C) (evaluation B C k ε))
    (1 ⊗ₜ[B] x)
  exact h.trans (by rw [evaluation_tmul, one_mul])

theorem trace_lift (z : C) (hz : (1 ⊗ₜ[B] z : k ⊗[B] C) = component B C k ε) (x : C) :
    algebraMap B k (Algebra.trace B C (z * x)) = ε x := by
  rw [← PeriodInvariants.AlgebraTraceBaseChange.includeRight B C k]
  have h : (1 ⊗ₜ[B] (z * x) : k ⊗[B] C) = (1 ⊗ₜ[B] z) * (1 ⊗ₜ[B] x) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [h, hz, trace_component_mul]

theorem exists_lift (h : Function.Surjective (algebraMap B k)) :
    ∃ z : C, (1 ⊗ₜ[B] z : k ⊗[B] C) = component B C k ε ∧
      ε z = 1 ∧ ∀ x : C, algebraMap B k (Algebra.trace B C (z * x)) = ε x := by
  obtain ⟨z, hz⟩ := Algebra.TensorProduct.includeRight_surjective C h (component B C k ε)
  refine ⟨z, hz, ?_, trace_lift B C k ε z hz⟩
  have he := congrArg (evaluation B C k ε) hz
  rw [component_evaluation] at he
  change (1 : k) * ε z = 1 at he
  simpa only [one_mul] using he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FiberSectionTrace
