import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Flat.Basic

/-! # Etale Domain Reduced -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleDomainReduced

noncomputable section

/-! # Flat étale algebras over a domain are reduced, by the actual fraction-field fibre -/

open scoped TensorProduct

universe u
variable (R S : Type u) [CommRing R] [IsDomain R] [CommRing S]
  [Algebra R S] [Module.Flat R S] [Algebra.Etale R S]

include R in
theorem reduced : IsReduced S := by
  let K := FractionRing R
  have : IsReduced (K ⊗[R] S) := Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[R] S)
  have hi : Function.Injective (Algebra.TensorProduct.includeRight : S →ₐ[R] K ⊗[R] S) :=
    Module.Flat.tensorProduct_mk_injective R S K
  exact isReduced_of_injective (Algebra.TensorProduct.includeRight : S →ₐ[R] K ⊗[R] S) hi

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleDomainReduced
