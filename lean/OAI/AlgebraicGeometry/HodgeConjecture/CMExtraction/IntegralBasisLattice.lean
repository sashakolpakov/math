import Mathlib.NumberTheory.NumberField.Basic

/-! # Integral Basis Lattice -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralBasisLattice.TestTransport

noncomputable section

/-! Integral-basis coordinates identify the actual ring-of-integers
lattice, including every rational scalar multiple of that lattice. -/

open scoped Classical _root_.NumberField

open _root_.NumberField _root_.Module

variable (F : Type) [Field F] [NumberField F]

theorem integralBasis_integral_iff (x : F) :
    (∀ i, ∃ z : ℤ, (z : ℚ) = (integralBasis F).equivFun x i) ↔
      ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = x := by
  constructor
  · intro h
    choose z hz using h
    refine ⟨(RingOfIntegers.basis F).equivFun.symm z, ?_⟩
    apply (integralBasis F).equivFun.injective
    funext i
    rw [Basis.equivFun_apply, integralBasis_repr_apply]
    change (((RingOfIntegers.basis F).equivFun
      ((RingOfIntegers.basis F).equivFun.symm z) i : ℤ) : ℚ) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hz i
  · rintro ⟨r, rfl⟩ i
    exact ⟨(RingOfIntegers.basis F).repr r i, (integralBasis_repr_apply F r i).symm⟩

theorem integralBasis_scaled_integral_iff (q : ℚ) (x : F) :
    (∀ i, ∃ z : ℤ, q * (z : ℚ) = (integralBasis F).equivFun x i) ↔
      ∃ r : 𝓞 F, algebraMap ℚ F q * algebraMap (𝓞 F) F r = x := by
  constructor
  · intro h
    choose z hz using h
    let r := (RingOfIntegers.basis F).equivFun.symm z
    have hr (i) : (integralBasis F).equivFun (algebraMap (𝓞 F) F r) i =
        (z i : ℚ) := by
      rw [Basis.equivFun_apply, integralBasis_repr_apply]
      change (((RingOfIntegers.basis F).equivFun
        ((RingOfIntegers.basis F).equivFun.symm z) i : ℤ) : ℚ) = _
      rw [LinearEquiv.apply_symm_apply]
    refine ⟨r, ?_⟩
    apply (integralBasis F).equivFun.injective
    funext i
    rw [← Algebra.smul_def]
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hr]
    exact hz i
  · rintro ⟨r, rfl⟩ i
    refine ⟨(RingOfIntegers.basis F).repr r i, ?_⟩
    rw [← Algebra.smul_def]
    rw [map_smul, Pi.smul_apply, smul_eq_mul, Basis.equivFun_apply,
      integralBasis_repr_apply]
    rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralBasisLattice.TestTransport
