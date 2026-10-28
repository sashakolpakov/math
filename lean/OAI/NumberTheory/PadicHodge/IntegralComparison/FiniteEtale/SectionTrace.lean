import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceDuality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SectionKernel

/-! # Section Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SectionTrace

noncomputable section

/-! The trace-dual of a genuine section of a finite étale algebra is
exactly its component idempotent. Its trace is one, without a degree
factor or a choice of trace normalization. -/
universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]
  (ε : A →ₐ[R] R) (e : A) (he : ε e = 1)
  (hker : ∀ x, ε x = 0 → e * x = 0)

include hker in
omit [Module.Free R A] [Module.Finite R A] in
theorem mul (x : A) : e * x = ε x • e := by
  have h := hker (x - algebraMap R A (ε x)) (by simp only [map_sub, ε.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self])
  rw [mul_sub, sub_eq_zero] at h
  exact h.trans (by rw [Algebra.smul_def, mul_comm])

omit [Module.Free R A] [Module.Finite R A] in
include he hker in
theorem idempotent : IsIdempotentElem e := by
  change e * e = e
  rw [mul R A ε e hker e, he, one_smul]

include he hker in
theorem trace_one : Algebra.trace R A e = 1 := by
  have h : Algebra.lmul R A e = ε.toLinearMap.smulRight e := by
    apply LinearMap.ext
    intro x
    exact mul R A ε e hker x
  rw [Algebra.trace_apply, h, LinearMap.trace_smulRight]
  exact he

include he hker in
theorem trace_mul (x : A) : Algebra.trace R A (e * x) = ε x := by
  rw [mul R A ε e hker x, map_smul, trace_one R A ε e he hker, smul_eq_mul, mul_one]

variable [Algebra.Etale R A]

include he hker in
theorem dual : TraceDuality.equiv R A e = ε.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact trace_mul R A ε e he hker x

include he hker in
theorem inverse : (TraceDuality.equiv R A).symm ε.toLinearMap = e := by
  apply (TraceDuality.equiv R A).injective
  rw [LinearEquiv.apply_symm_apply, dual R A ε e he hker]

def component : A := (IntegralComparison.Etale.SectionKernel.exists_annihilator ε).choose

omit [Module.Free R A] [Module.Finite R A] in
theorem component_evaluation : ε (component R A ε) = 1 :=
  (IntegralComparison.Etale.SectionKernel.exists_annihilator ε).choose_spec.1

omit [Module.Free R A] [Module.Finite R A] in
theorem component_annihilates (x : A) (hx : ε x = 0) : component R A ε * x = 0 :=
  (IntegralComparison.Etale.SectionKernel.exists_annihilator ε).choose_spec.2 x hx

theorem inverse_eq_component : (TraceDuality.equiv R A).symm ε.toLinearMap =
    component R A ε :=
  inverse R A ε (component R A ε) (component_evaluation R A ε) (component_annihilates R A ε)

theorem component_trace : Algebra.trace R A (component R A ε) = 1 :=
  trace_one R A ε (component R A ε) (component_evaluation R A ε) (component_annihilates R A ε)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SectionTrace
