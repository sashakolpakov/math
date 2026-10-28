import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! # Etale Domain Reduced -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EtaleDomainReduced

noncomputable section

/-! Flat unramified algebras of essentially finite type over domains are reduced, by embedding in their generic fiber. -/

open scoped TensorProduct

universe u v

theorem flat_unramified_domain_isReduced (R : Type u) (S : Type v)
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S] : IsReduced S := by
  let K := FractionRing R
  let f := Algebra.TensorProduct.includeRight (R := R) (A := K) (B := S)
  have hf : Function.Injective f := by
    have h : ⇑f = (LinearMap.rTensor S (Algebra.ofId R K).toLinearMap).comp
        (Algebra.TensorProduct.lid R S).symm.toLinearMap := by
      ext x
      simp [f]
    rw [h]
    have hi : Function.Injective (LinearMap.rTensor S (Algebra.ofId R K).toLinearMap) :=
      Module.Flat.rTensor_preserves_injective_linearMap (Algebra.ofId R K).toLinearMap
        (IsFractionRing.injective R K)
    exact hi.comp (Algebra.TensorProduct.lid R S).symm.injective
  have : IsReduced (K ⊗[R] S) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective f hf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EtaleDomainReduced
