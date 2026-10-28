import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Semilinear Tensor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearTensor.SemilinearTensorExtension

noncomputable section

/-! Extending an actual semilinear equivalence along compatible coefficient-ring equivalences. -/

open scoped TensorProduct

variable {R S F G : Type*} [CommRing R] [CommRing S] [CommRing F] [CommRing G]
  [Algebra R F] [Algebra S G]
  (e : R ≃+* S) (φ : F ≃+* G)
  (h : ∀ r : R, φ (algebraMap R F r) = algebraMap S G (e r))

local instance baseInvPair : RingHomInvPair e.toRingHom e.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv e
local instance baseInvPairSymm : RingHomInvPair e.symm.toRingHom e.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm e
local instance fieldInvPair : RingHomInvPair φ.toRingHom φ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv φ
local instance fieldInvPairSymm : RingHomInvPair φ.symm.toRingHom φ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm φ

def scalarEquiv : F ≃ₛₗ[e.toRingHom] G where
  __ := φ.toAddEquiv
  map_smul' r x := by
    change φ (r • x) = e r • φ x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, h]

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
  (f : M ≃ₛₗ[e.toRingHom] N)

def equiv : (F ⊗[R] M) ≃ₛₗ[φ.toRingHom] (G ⊗[S] N) where
  __ := (TensorProduct.congr (scalarEquiv e φ h) f).toAddEquiv
  map_smul' a x := by
    change TensorProduct.congr (scalarEquiv e φ h) f (a • x) =
      φ a • TensorProduct.congr (scalarEquiv e φ h) f x
    induction x using TensorProduct.inductionOn with
    | tmul b m =>
      simp only [TensorProduct.smul_tmul', TensorProduct.congr_tmul]
      exact congrArg (fun c : G => c ⊗ₜ[S] f m) (φ.map_mul a b)
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem equiv_tmul (a : F) (m : M) : equiv e φ h f (a ⊗ₜ[R] m) = φ a ⊗ₜ[S] f m := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearTensor.SemilinearTensorExtension
