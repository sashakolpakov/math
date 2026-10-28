import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.NilReductionEquiv

/-! # Nil Common Reduction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.NilCommonReduction

noncomputable section

/-! Affine smooth models with specified maps to the same actual special
fiber have an isomorphism which induces that exact identification. -/
universe u v w z
variable {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A]
  {B : Type w} [CommRing B] [Algebra R B]
  {C : Type z} [CommRing C] [Algebra R C]
  (I : Ideal R)

def quotientEquiv (π : A →ₐ[R] C) (hπ : Function.Surjective π)
    (hker : RingHom.ker π.toRingHom = I.map (algebraMap R A)) :
    (A ⧸ I.map (algebraMap R A)) ≃ₐ[R] C :=
  (Ideal.quotientEquivAlgOfEq R hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hπ)

theorem quotientEquiv_mk (π : A →ₐ[R] C) (hπ : Function.Surjective π)
    (hker : RingHom.ker π.toRingHom = I.map (algebraMap R A)) (a : A) :
    quotientEquiv I π hπ hker (Ideal.Quotient.mk _ a) = π a := rfl

variable (hI : IsNilpotent I) [Algebra.FormallySmooth R A] [Module.Flat R B]
  (πA : A →ₐ[R] C) (hA : Function.Surjective πA)
  (hAker : RingHom.ker πA.toRingHom = I.map (algebraMap R A))
  (πB : B →ₐ[R] C) (hB : Function.Surjective πB)
  (hBker : RingHom.ker πB.toRingHom = I.map (algebraMap R B))

include hI hA hAker hB hBker in
theorem exists_equiv : ∃ e : A ≃ₐ[R] B, πB.comp e.toAlgHom = πA := by
  let eA := quotientEquiv I πA hA hAker
  let eB := quotientEquiv I πB hB hBker
  obtain ⟨e, he⟩ := NilReductionEquiv.exists_equiv I hI (eA.trans eB.symm)
  refine ⟨e, AlgHom.ext fun a => ?_⟩
  have h := congrArg eB (AlgHom.congr_fun he a)
  change eB (Ideal.Quotient.mk _ (e a)) = eB (eB.symm (eA (Ideal.Quotient.mk _ a))) at h
  rw [eB.apply_symm_apply] at h
  exact h

def equiv : A ≃ₐ[R] B :=
  (exists_equiv I hI πA hA hAker πB hB hBker).choose

theorem reduction_equiv : πB.comp (equiv I hI πA hA hAker πB hB hBker).toAlgHom = πA :=
  (exists_equiv I hI πA hA hAker πB hB hBker).choose_spec

theorem reduction_equiv_apply (a : A) :
    πB (equiv I hI πA hA hAker πB hB hBker a) = πA a :=
  AlgHom.congr_fun (reduction_equiv I hI πA hA hAker πB hB hBker) a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.NilCommonReduction
