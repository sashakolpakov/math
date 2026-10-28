import OAI.AlgebraicGeometry.Divisors.LineBundles.ExactSequenceLength
import OAI.AlgebraicGeometry.Divisors.LineBundles.SubquotientImage

/-! # Nested Quotient Length -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.NestedQuotientLength.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: length of two nested quotients

The successive quotient is the actual image of the larger submodule
in the smaller quotient. The third isomorphism theorem identifies the
remaining quotient, and short exact length additivity gives the formula.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem moduleLengthNat_nestedQuotient (P Q : Submodule R M) (hPQ : P ≤ Q)
    (hP : Module.length R (M ⧸ P) ≠ ⊤) :
    (Module.length R (M ⧸ P)).toNat =
      (Module.length R (Q ⧸ P.comap Q.subtype)).toNat +
      (Module.length R (M ⧸ Q)).toNat := by
  have h := ExactSequenceLength.BundleCycles.moduleLengthNat_shortExact (Q.map P.mkQ).subtype (Q.map P.mkQ).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _) hP
  rw [← (SubquotientImage.BundleCycles.subquotientImageEquiv P Q).length_eq,
    (Submodule.quotientQuotientEquivQuotient P Q hPQ).length_eq] at h
  exact h

end

/-!
# LineBundleCycles: the length gained by scaling an image

The image of x times a linear map is x times its original image.
Its successive quotient is therefore the actual multiplication
cokernel on that image.
-/

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

theorem scaledRange_le (x : R) (f : N →ₗ[R] M) : (x • f).range ≤ f.range := by
  rintro _ ⟨n, rfl⟩
  exact ⟨x • n, f.map_smul x n⟩

theorem scaledRange_comap_rangeSubtype (x : R) (f : N →ₗ[R] M) :
    (x • f).range.comap f.range.subtype = (MultiplicationSequence.BundleCycles.equationEndomorphism x f.range).range := by
  ext m
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨⟨f n, ⟨n, rfl⟩⟩, Subtype.ext hn⟩
  · rintro ⟨n, rfl⟩
    obtain ⟨k, hk⟩ := n.2
    exact ⟨k, congrArg (fun m : M => x • m) hk⟩

theorem moduleLengthNat_scaledRangeQuotient (x : R) (f : N →ₗ[R] M)
    (h : Module.length R (M ⧸ (x • f).range) ≠ ⊤) :
    (Module.length R (M ⧸ (x • f).range)).toNat =
      (Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x f.range)).toNat +
      (Module.length R (M ⧸ f.range)).toNat := by
  have he := moduleLengthNat_nestedQuotient (x • f).range f.range (scaledRange_le x f) h
  rw [scaledRange_comap_rangeSubtype] at he
  exact he

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.NestedQuotientLength.BundleCycles
