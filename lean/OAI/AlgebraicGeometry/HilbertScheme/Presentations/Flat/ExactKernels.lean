import Mathlib.RingTheory.Flat.Equalizer

/-! # Exact Kernels -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ExactKernels

/-! Kernels in short exact sequences of flat modules are flat. -/

universe u v w t

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type t} [AddCommGroup P] [Module R P]

theorem flat_of_exact_flat_quotient [Module.Flat R N] [Module.Flat R P]
    (i : M →ₗ[R] N) (p : N →ₗ[R] P) (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) : Module.Flat R M := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro U V _ _ _ _ f hf
  apply Function.Injective.of_comp (f := i.lTensor V)
  have hcomm : (i.lTensor V).comp (f.rTensor M) = (f.rTensor N).comp (i.lTensor U) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  change Function.Injective ((i.lTensor V).comp (f.rTensor M))
  rw [hcomm]
  exact (Module.Flat.rTensor_preserves_injective_linearMap (M := N) f hf).comp
    (LinearMap.lTensor_injective_of_exact_of_flat p hp i hi hex U)

theorem kernel_flat_of_surjective [Module.Flat R N] [Module.Flat R P]
    (p : N →ₗ[R] P) (hp : Function.Surjective p) : Module.Flat R p.ker :=
  flat_of_exact_flat_quotient p.ker.subtype p p.ker.subtype_injective hp (LinearMap.exact_subtype_ker_map p)

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ExactKernels
