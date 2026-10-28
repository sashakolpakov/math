import Mathlib.RingTheory.Localization.BaseChange

/-! # Tensor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.TensorComparison

noncomputable section

/-! An invertible tensor comparison over a localized coefficient ring proves module localization. -/

open TensorProduct

variable {R B V G : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable [AddCommGroup V] [Module R V] [AddCommGroup G] [Module R G]

theorem isLocalizedModule_of_tensor_comparison (S : Submonoid R) [IsLocalization S B]
    (a : V →ₗ[R] G) (c : TensorProduct R B V →ₗ[R] G)
    (hc : Function.Bijective c) (hunit : ∀ v, c (1 ⊗ₜ[R] v) = a v) :
    IsLocalizedModule S a := by
  have : IsLocalizedModule S (TensorProduct.mk R B V 1) :=
    (isLocalizedModule_iff_isBaseChange S B (TensorProduct.mk R B V 1)).mpr
      (TensorProduct.isBaseChange (R := R) (S := B) (M := V))
  let e : TensorProduct R B V ≃ₗ[R] G := LinearEquiv.ofBijective c hc
  have he : e.toLinearMap.comp (TensorProduct.mk R B V 1) = a := by
    ext v
    exact hunit v
  have h := IsLocalizedModule.of_linearEquiv S (TensorProduct.mk R B V 1) e
  rw [he] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.TensorComparison
