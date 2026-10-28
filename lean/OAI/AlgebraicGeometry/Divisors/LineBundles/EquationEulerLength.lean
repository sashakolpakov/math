import OAI.AlgebraicGeometry.Divisors.LineBundles.ExactSequenceLength

/-! # Equation Euler Length -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.EquationEulerLength.BundleCycles

noncomputable section

/-!
# LineBundleCycles: additivity of the finite multiplication Euler length

The local intersection invariant is cokernel length minus kernel length
for multiplication by the equation. Both lengths are required finite.
The actual multiplication snake sequence proves additivity across a
submodule and quotient. Modules of finite length contribute zero.
-/

variable {R : Type*} [CommRing R]

/-- Cokernel length minus kernel length, with both finiteness conditions explicit. -/
def equationEulerLength (a : R) (M : Type*) [AddCommGroup M] [Module R M]
    (_hK : Module.length R (MultiplicationSequence.BundleCycles.equationKernel a M) ≠ ⊤)
    (_hC : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel a M) ≠ ⊤) : ℤ :=
  ((Module.length R (MultiplicationSequence.BundleCycles.equationCokernel a M)).toNat : ℤ) - (Module.length R (MultiplicationSequence.BundleCycles.equationKernel a M)).toNat

/-- The exact snake sequence proves additivity without any injectivity assumption on multiplication. -/
theorem equationEulerLength_additive (a : R) {M : Type*} [AddCommGroup M] [Module R M]
    (P : Submodule R M)
    (hKP : Module.length R (MultiplicationSequence.BundleCycles.equationKernel a P) ≠ ⊤)
    (hCP : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel a P) ≠ ⊤)
    (hKM : Module.length R (MultiplicationSequence.BundleCycles.equationKernel a M) ≠ ⊤)
    (hCM : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel a M) ≠ ⊤)
    (hKQ : Module.length R (MultiplicationSequence.BundleCycles.equationKernel a (M ⧸ P)) ≠ ⊤)
    (hCQ : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel a (M ⧸ P)) ≠ ⊤) :
    equationEulerLength a M hKM hCM =
      equationEulerLength a P hKP hCP + equationEulerLength a (M ⧸ P) hKQ hCQ := by
  have h := ExactSequenceLength.BundleCycles.moduleLengthNat_sixTerm (MultiplicationSequence.BundleCycles.equationKernelInclusion a P) (MultiplicationSequence.BundleCycles.equationKernelQuotient a P)
    (MultiplicationSequence.BundleCycles.equationSnakeBoundary a P) (MultiplicationSequence.BundleCycles.equationCokernelInclusion a P) (MultiplicationSequence.BundleCycles.equationCokernelQuotient a P)
    (MultiplicationSequence.BundleCycles.equationKernelInclusion_injective a P) (MultiplicationSequence.BundleCycles.equationCokernelQuotient_surjective a P)
    (MultiplicationSequence.BundleCycles.equationKernel_exact a P) (MultiplicationSequence.BundleCycles.equationSnake_kernel_exact a P) (MultiplicationSequence.BundleCycles.equationSnake_cokernel_exact a P)
    (MultiplicationSequence.BundleCycles.equationCokernel_exact a P) hKM hKQ hCP hCM
  unfold equationEulerLength
  omega

/-- Finite ambient length implies finite length of the multiplication kernel. -/
theorem equationKernel_length_ne_top (a : R) (M : Type*) [AddCommGroup M] [Module R M]
    (hM : Module.length R M ≠ ⊤) : Module.length R (MultiplicationSequence.BundleCycles.equationKernel a M) ≠ ⊤ :=
  ne_top_of_le_ne_top hM (Module.length_le_of_injective (MultiplicationSequence.BundleCycles.equationKernel a M).subtype
    (Submodule.subtype_injective _))

/-- Finite ambient length implies finite length of the multiplication cokernel. -/
theorem equationCokernel_length_ne_top (a : R) (M : Type*) [AddCommGroup M] [Module R M]
    (hM : Module.length R M ≠ ⊤) : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel a M) ≠ ⊤ :=
  ne_top_of_le_ne_top hM (Module.length_le_of_surjective (MultiplicationSequence.BundleCycles.equationEndomorphism a M).range.mkQ
    (Submodule.mkQ_surjective _))

/-- A finite-length module contributes zero to the divisor intersection invariant. -/
theorem equationEulerLength_zero_of_finite (a : R) (M : Type*) [AddCommGroup M] [Module R M]
    (hK : Module.length R (MultiplicationSequence.BundleCycles.equationKernel a M) ≠ ⊤)
    (hC : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel a M) ≠ ⊤)
    (hM : Module.length R M ≠ ⊤) : equationEulerLength a M hK hC = 0 := by
  let u := MultiplicationSequence.BundleCycles.equationEndomorphism a M
  have he : Function.Exact u.ker.subtype u.rangeRestrict := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, congrArg Subtype.val hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact Subtype.ext y.2
  have h₁ := ExactSequenceLength.BundleCycles.moduleLengthNat_shortExact u.ker.subtype u.rangeRestrict
    u.ker.subtype_injective u.surjective_rangeRestrict he hM
  have h₂ := ExactSequenceLength.BundleCycles.moduleLengthNat_shortExact u.range.subtype u.range.mkQ
    u.range.subtype_injective u.range.mkQ_surjective (LinearMap.exact_subtype_mkQ u.range) hM
  change ((Module.length R (M ⧸ u.range)).toNat : ℤ) - (Module.length R u.ker).toNat = 0
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.EquationEulerLength.BundleCycles
