import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Cube Tensor Pushout Coordinates -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeTensorPushoutCoordinates.Construction.CubeCech

noncomputable section

/-! Tensor coordinates for a categorical pushout of commutative algebras. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable {k : Type u} [CommRing k] (A B : CommAlgCat.{u} k) (C : CommRingCat.{u})
    (a : CommRingCat.of A ⟶ C) (b : CommRingCat.of B ⟶ C)
    (H : IsPushout (CommRingCat.ofHom (algebraMap k A)) (CommRingCat.ofHom (algebraMap k B)) a b)

def tensorPushoutRingEquiv : A ⊗[k] B ≃+* C :=
  ((CommRingCat.isPushout_tensorProduct k A B).isoIsPushout _ _ H).commRingCatIsoToRingEquiv

theorem tensorPushoutRingEquiv_left (x : A) :
    tensorPushoutRingEquiv A B C a b H (x ⊗ₜ[k] (1 : B)) = a x := by
  exact congrArg (fun q : CommRingCat.of A ⟶ C ↦ q x)
    ((CommRingCat.isPushout_tensorProduct k A B).inl_isoIsPushout_hom _ _ H)

theorem tensorPushoutRingEquiv_right (y : B) :
    tensorPushoutRingEquiv A B C a b H ((1 : A) ⊗ₜ[k] y) = b y := by
  exact congrArg (fun q : CommRingCat.of B ⟶ C ↦ q y)
    ((CommRingCat.isPushout_tensorProduct k A B).inr_isoIsPushout_hom _ _ H)

theorem tensorPushoutRingEquiv_tmul (x : A) (y : B) :
    tensorPushoutRingEquiv A B C a b H (x ⊗ₜ[k] y) = a x * b y := by
  have ht : x ⊗ₜ[k] y = (x ⊗ₜ[k] (1 : B)) * ((1 : A) ⊗ₜ[k] y) := by simp
  rw [ht, map_mul, tensorPushoutRingEquiv_left, tensorPushoutRingEquiv_right]

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeTensorPushoutCoordinates.Construction.CubeCech
