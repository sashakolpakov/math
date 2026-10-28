import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Regular Tensor Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.RegularTensorBaseChange.BundleCycles

noncomputable section

/-! A regular equation with flat quotient remains regular after
arbitrary coefficient base change. -/

open TensorProduct

variable (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (t : A) (ht : IsRegular t)

include ht in
theorem regular_tensor_baseChange_of_flat_cokernel
    {C : Type} [AddCommGroup C] [Module R C] [Module.Flat R C]
    (q : A →ₗ[R] C) (hq : Function.Surjective q)
    (hk : ∀ a, q a = 0 ↔ a ∈ Ideal.span {t}) :
    IsRegular (1 ⊗ₜ[R] t : B ⊗[R] A) := by
  let m : A →ₗ[R] A := LinearMap.mulLeft R t
  have hm : Function.Injective m := ht.left
  have hExact : Function.Exact m q := by
    intro a
    change q a = 0 ↔ ∃ b, t * b = a
    rw [hk a, Ideal.mem_span_singleton]
    simp only [dvd_def, eq_comm]
  have hInj := LinearMap.lTensor_injective_of_exact_of_flat q hq m hm hExact B
  have hMul (z : B ⊗[R] A) : m.lTensor B z = (1 ⊗ₜ[R] t) * z := by
    induction z using TensorProduct.inductionOn with
    | tmul b a => simp only [LinearMap.lTensor_tmul, m, LinearMap.mulLeft_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | add z w hz hw => rw [map_add, mul_add, hz, hw]
  have hleft : IsLeftRegular (1 ⊗ₜ[R] t : B ⊗[R] A) := by
    intro z w h
    exact hInj ((hMul z).trans (h.trans (hMul w).symm))
  exact ⟨hleft, fun z w h => hleft ((mul_comm _ _).trans (h.trans (mul_comm _ _)))⟩

include ht in
theorem regular_tensor_baseChange [Module.Flat R (A ⧸ Ideal.span {t})] :
    IsRegular (1 ⊗ₜ[R] t : B ⊗[R] A) :=
  regular_tensor_baseChange_of_flat_cokernel R A B t ht
    (Ideal.Quotient.mkₐ R (Ideal.span {t})).toLinearMap Ideal.Quotient.mk_surjective
    (fun _ => Ideal.Quotient.eq_zero_iff_mem)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.RegularTensorBaseChange.BundleCycles
