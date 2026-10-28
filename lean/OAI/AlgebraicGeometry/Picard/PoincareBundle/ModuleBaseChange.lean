import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Module Base Change -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChange

noncomputable section

/-!
# Affine module base change for PoincareBundle

The base-change formula for direct image along an affine morphism is
the canonical tensor equivalence `(S ⊗[R] T) ⊗[S] M ≃ T ⊗[R] M`.
The formula on pure tensors is retained for comparison with adjunction mates.
-/

open TensorProduct
open scoped TensorProduct

universe u

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]
  (M : Type u) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- The underlying R-linear affine base-change equivalence. -/
def baseChangeEquivR : ((S ⊗[R] T) ⊗[S] M) ≃ₗ[R] T ⊗[R] M :=
  ((TensorProduct.comm S (S ⊗[R] T) M).restrictScalars R).trans
    (((AlgebraTensorModule.cancelBaseChange R S S M T).restrictScalars R).trans
      (TensorProduct.comm R M T))

@[simp]
theorem baseChangeEquivR_tmul (s : S) (t : T) (m : M) :
    baseChangeEquivR R S T M ((s ⊗ₜ[R] t) ⊗ₜ[S] m) = t ⊗ₜ[R] (s • m) := by
  simp [baseChangeEquivR, AlgebraTensorModule.cancelBaseChange]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The second coordinate ring acts on its own tensor factor. -/
theorem right_smul_tmul (s : S) (t t' : T) :
    t • (s ⊗ₜ[R] t' : S ⊗[R] T) = s ⊗ₜ[R] (t * t') := by
  rw [Algebra.smul_def]
  change (1 ⊗ₜ[R] t : S ⊗[R] T) * (s ⊗ₜ[R] t') = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- The tensor base-change equivalence is linear over the new base ring. -/
def baseChangeEquiv : ((S ⊗[R] T) ⊗[S] M) ≃ₗ[T] T ⊗[R] M where
  __ := (baseChangeEquivR R S T M).toAddEquiv
  map_smul' t z := by
    change baseChangeEquivR R S T M (t • z) = t • baseChangeEquivR R S T M z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul x m =>
        induction x using TensorProduct.inductionOn with
        | add x y hx hy => simp only [smul_add, add_tmul, map_add, hx, hy]
        | tmul s t' =>
            rw [smul_tmul', right_smul_tmul, baseChangeEquivR_tmul,
              baseChangeEquivR_tmul, smul_tmul', smul_eq_mul]

@[simp]
theorem baseChangeEquiv_tmul (s : S) (t : T) (m : M) :
    baseChangeEquiv R S T M ((s ⊗ₜ[R] t) ⊗ₜ[S] m) = t ⊗ₜ[R] (s • m) :=
  baseChangeEquivR_tmul R S T M s t m

@[simp]
theorem baseChangeEquiv_symm_tmul (t : T) (m : M) :
    (baseChangeEquiv R S T M).symm (t ⊗ₜ[R] m) = (1 ⊗ₜ[R] t) ⊗ₜ[S] m := by
  apply (baseChangeEquiv R S T M).injective
  rw [LinearEquiv.apply_symm_apply, baseChangeEquiv_tmul, one_smul]

variable {M} {N : Type u} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- Affine base change is natural in the original module. -/
theorem baseChangeEquiv_naturality (a : M →ₗ[S] N) (z : (S ⊗[R] T) ⊗[S] M) :
    baseChangeEquiv R S T N (TensorProduct.map (LinearMap.id : (S ⊗[R] T) →ₗ[S] _) a z) =
      TensorProduct.map (LinearMap.id : T →ₗ[R] T) (a.restrictScalars R)
        (baseChangeEquiv R S T M z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x m =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
      | tmul s t => simp [a.map_smul]

/-- The inverse base-change map is the canonical map sending a pure
tensor to the corresponding scalar extended tensor. -/
theorem baseChangeEquiv_symm_naturality (a : M →ₗ[S] N) (z : T ⊗[R] M) :
    (baseChangeEquiv R S T N).symm
        (TensorProduct.map (LinearMap.id : T →ₗ[R] T) (a.restrictScalars R) z) =
      TensorProduct.map (LinearMap.id : (S ⊗[R] T) →ₗ[S] _) a
        ((baseChangeEquiv R S T M).symm z) := by
  apply (baseChangeEquiv R S T N).injective
  rw [LinearEquiv.apply_symm_apply, baseChangeEquiv_naturality, LinearEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChange
