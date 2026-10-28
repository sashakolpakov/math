import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleHomDerivation
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Fiber Tensor Restriction Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FiberTensorRestrictionDetection

noncomputable section

/-! The original affine functions surject onto a fiber at a rational
base point. Equality with the etale restriction of a fiber derivation
can therefore be tested on those original functions. -/

open scoped TensorProduct

variable (k R A : Type) [CommRing k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra R k] [IsScalarTower k R k] [Algebra R A]

theorem rationalBasePoint_surjective : Function.Surjective (algebraMap R k) := by
  intro c
  refine ⟨algebraMap k R c, ?_⟩
  rw [← IsScalarTower.algebraMap_apply k R k, Algebra.algebraMap_self_apply]

theorem pointFiberTensor_original_surjective :
    Function.Surjective (Algebra.TensorProduct.includeRight : A →ₐ[R] k ⊗[R] A) :=
  Algebra.TensorProduct.includeRight_surjective A (rationalBasePoint_surjective k R)

variable (D : Type) [CommRing D] [Algebra R D]

theorem pointFiberTensorDerivation_restriction_of_original (q : A →ₐ[R] D)
    (hq : (Algebra.TensorProduct.map (AlgHom.id k k) q).toRingHom.Etale)
    (d : Derivation k (k ⊗[R] A) (k ⊗[R] A)) (e : Derivation k (k ⊗[R] D) (k ⊗[R] D))
    (h : ∀ a, e ((1 : k) ⊗ₜ[R] q a) =
      Algebra.TensorProduct.map (AlgHom.id k k) q (d ((1 : k) ⊗ₜ[R] a))) :
    e = EtaleHomDerivation.etaleAlgHomDerivationLinear (Algebra.TensorProduct.map (AlgHom.id k k) q) hq d := by
  apply EtaleHomDerivation.etaleAlgHomDerivationLinear_unique
  intro b
  obtain ⟨a, rfl⟩ := pointFiberTensor_original_surjective k R A b
  exact h a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FiberTensorRestrictionDetection
