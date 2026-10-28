import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Surjective Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveBaseChange

noncomputable section

/-! The kernel of the canonical base-change map for a surjective coefficient algebra. -/

open scoped TensorProduct

universe u v w

variable {R : Type u} [CommRing R] (S : Type v) (A : Type w)
  [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
  (h : Function.Surjective (algebraMap R S))

def quotientEquiv :
    (A ⧸ (RingHom.ker (algebraMap R S)).map (algebraMap R A)) ≃ₐ[R] S ⊗[R] A :=
  ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor A (RingHom.ker (algebraMap R S))).restrictScalars R).trans
    (Algebra.TensorProduct.congr
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) h) (AlgEquiv.refl : A ≃ₐ[R] A))

theorem quotientEquiv_mk (a : A) :
    quotientEquiv S A h (Ideal.Quotient.mk _ a) = 1 ⊗ₜ[R] a := by
  change Algebra.TensorProduct.congr
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) h) (AlgEquiv.refl : A ≃ₐ[R] A)
      (1 ⊗ₜ[R] a) = _
  simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    map_one, AlgEquiv.coe_toAlgHom]
  rfl

include h in
theorem kernel : RingHom.ker (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom =
    (RingHom.ker (algebraMap R S)).map (algebraMap R A) := by
  ext a
  change (1 ⊗ₜ[R] a : S ⊗[R] A) = 0 ↔ a ∈ _
  rw [← quotientEquiv_mk S A h]
  constructor
  · intro ha
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((quotientEquiv S A h).injective (ha.trans (map_zero (quotientEquiv S A h)).symm))
  · intro ha
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact map_zero _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveBaseChange
