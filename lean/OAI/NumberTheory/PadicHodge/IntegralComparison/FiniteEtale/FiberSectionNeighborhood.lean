import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FiberSectionTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionKernel

/-! # Fiber Section Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FiberSectionNeighborhood.Trace

noncomputable section

/-! A lift of the trace-dual fiber component selects a genuine source
principal neighborhood. On that neighborhood the pulled-back target
parameters generate exactly the kernel of the chosen source section. -/
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable (B C k : Type u) [CommRing B] [CommRing C] [CommRing k]
  [Algebra B C] [Algebra B k] [Module.Free B C] [Module.Finite B C]
  [Algebra.Etale B C] (ε : C →ₐ[B] k)
  (h : Function.Surjective (algebraMap B k))

def fiberIdeal : Ideal C := (RingHom.ker (algebraMap B k)).map (algebraMap B C)

omit [Module.Free B C] [Module.Finite B C] [Algebra.Etale B C] in
theorem fiberIdeal_le : fiberIdeal B C k ≤ RingHom.ker ε.toRingHom := by
  rw [fiberIdeal, Ideal.map_le_iff_le_comap]
  intro x hx
  change ε (algebraMap B C x) = 0
  rw [ε.commutes]
  exact hx

include h in
omit [Module.Free B C] [Module.Finite B C] in
theorem lift_annihilates (z : C)
    (hz : (1 ⊗ₜ[B] z : k ⊗[B] C) = FiberSectionTrace.component B C k ε)
    (x : C) (hx : ε x = 0) : z*x ∈ fiberIdeal B C k := by
  rw [fiberIdeal, ← SurjectiveBaseChange.kernel k C h]
  change (1 ⊗ₜ[B] (z*x) : k ⊗[B] C) = 0
  have hm : (1 ⊗ₜ[B] (z*x) : k ⊗[B] C) =
      (1 ⊗ₜ[B] z) * (1 ⊗ₜ[B] x) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [hm, hz]
  apply SectionTrace.component_annihilates k (k ⊗[B] C)
    (FiberSectionTrace.evaluation B C k ε)
  rw [FiberSectionTrace.evaluation_tmul, hx, mul_zero]

variable (z : C) (hz : (1 ⊗ₜ[B] z : k ⊗[B] C) = FiberSectionTrace.component B C k ε)
  (S : Type v) [CommRing S] [Algebra C S] [IsLocalization.Away z S]
  (η : S →+* k) (hη : η.comp (algebraMap C S) = ε.toRingHom)

include h hz hη in
omit [Module.Free B C] [Module.Finite B C] in
theorem localized_kernel : RingHom.ker η = (fiberIdeal B C k).map (algebraMap C S) :=
  Principal.SectionKernel.kernel z ε.toRingHom η hη (fiberIdeal B C k)
    (fiberIdeal_le B C k ε) (lift_annihilates B C k ε h z hz)

include h hz hη in
omit [Module.Free B C] [Module.Finite B C] in
theorem localized_parameter_kernel {m : ℕ} (t : Fin m → B)
    (ht : RingHom.ker (algebraMap B k) = Ideal.span (Set.range t)) :
    RingHom.ker η = Ideal.span (Set.range (algebraMap C S ∘ algebraMap B C ∘ t)) := by
  rw [localized_kernel B C k ε h z hz S η hη, fiberIdeal, ht,
    Ideal.map_span, ← Set.range_comp, Ideal.map_span, ← Set.range_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FiberSectionNeighborhood.Trace
