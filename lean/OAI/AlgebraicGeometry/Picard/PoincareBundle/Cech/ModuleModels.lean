import OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtensionTwist
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeFunctor
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Module Models -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels

noncomputable section

/-!
# Tensor models for the two actual affine Čech pullbacks for PoincareBundle
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The first projection of the affine kernel pair, on coordinate rings. -/
def firstMap : S →+* S ⊗[R] S := algebraMap S (S ⊗[R] S)

/-- The second projection of the affine kernel pair, on coordinate rings. -/
def secondMap : S →+* S ⊗[R] S := Algebra.TensorProduct.includeRight.toRingHom

/-- Interchanging the two factors interchanges the projection maps. -/
theorem flip_second (s : S) :
    Algebra.TensorProduct.comm R S S (secondMap R S s) = firstMap R S s := rfl

/-- The actual module pulled back along the first projection. -/
abbrev firstPullback (M : ModuleCat.{u} S) := (extendScalars (firstMap R S)).obj M

/-- The actual module pulled back along the second projection. -/
abbrev secondPullback (M : ModuleCat.{u} S) := (extendScalars (secondMap R S)).obj M

variable (M : ModuleCat.{u} S)

/-- Swapping coordinates identifies the two pullback modules semilinearly. -/
def flipPullback : secondPullback R S M ≃+ firstPullback R S M :=
  ExtensionTwist.extensionEquiv (secondMap R S) (firstMap R S)
    (Algebra.TensorProduct.comm R S S).toRingEquiv (flip_second R S) M

/-- The first pullback in the usual coefficient/module tensor model. -/
def firstModel : firstPullback R S M ≃+
    S ⊗[R] (restrictScalars (algebraMap R S)).obj M := by
  let e := ModuleBaseChangeFunctor.targetModelEquiv R S S M
  let d := ModuleBaseChange.baseChangeEquiv R S S
    ((restrictScalars (algebraMap R S)).obj M)
  exact {
    toFun := fun z => d (e z)
    invFun := fun z => e.symm (d.symm z)
    left_inv := fun z =>
      (congrArg e.symm (d.symm_apply_apply (e z))).trans (e.symm_apply_apply z)
    right_inv := fun z =>
      (congrArg d (e.apply_symm_apply (d.symm z))).trans (d.apply_symm_apply z)
    map_add' := fun x y => (congrArg d (e.map_add x y)).trans (d.map_add (e x) (e y)) }

/-- The second pullback uses the other coordinate as its coefficient factor. -/
def secondModel : secondPullback R S M ≃+
    S ⊗[R] (restrictScalars (algebraMap R S)).obj M :=
  (flipPullback R S M).trans (firstModel R S M)

@[simp]
theorem firstModel_tmul (s t : S) (m : M) :
    firstModel R S M ((s ⊗ₜ[R] t) ⊗ₜ[S,firstMap R S] m) =
      t ⊗ₜ[R] (s • (show (restrictScalars (algebraMap R S)).obj M from m)) := by
  change ModuleBaseChange.baseChangeEquiv R S S
    ((restrictScalars (algebraMap R S)).obj M)
      ((ModuleBaseChangeFunctor.targetModelEquiv R S S M)
        ((s ⊗ₜ[R] t) ⊗ₜ[S,firstMap R S] m)) = _
  exact ModuleBaseChange.baseChangeEquiv_tmul R S S
    ((restrictScalars (algebraMap R S)).obj M) s t m

@[simp]
theorem secondModel_tmul (s t : S) (m : M) :
    secondModel R S M ((s ⊗ₜ[R] t) ⊗ₜ[S,secondMap R S] m) =
      s ⊗ₜ[R] (t • (show (restrictScalars (algebraMap R S)).obj M from m)) := by
  change firstModel R S M
    ((Algebra.TensorProduct.comm R S S (s ⊗ₜ[R] t)) ⊗ₜ[S,firstMap R S] m) = _
  rw [Algebra.TensorProduct.comm_tmul, firstModel_tmul]

/-- In the first model, the second coordinate acts on the coefficient factor. -/
theorem firstModel_second_smul (s : S) (z : firstPullback R S M) :
    firstModel R S M (secondMap R S s • z) = s • firstModel R S M z := by
  let e := ModuleBaseChangeFunctor.targetModelEquiv R S S M
  let d := ModuleBaseChange.baseChangeEquiv R S S
    ((restrictScalars (algebraMap R S)).obj M)
  exact (congrArg d (e.map_smul s z)).trans (d.map_smul s (e z))

/-- In the second model, the first coordinate acts on the coefficient factor. -/
theorem secondModel_first_smul (s : S) (z : secondPullback R S M) :
    secondModel R S M (firstMap R S s • z) = s • secondModel R S M z := by
  have h := ExtensionTwist.extensionEquiv_smul (secondMap R S) (firstMap R S)
    (Algebra.TensorProduct.comm R S S).toRingEquiv (flip_second R S) M (firstMap R S s) z
  change firstModel R S M (flipPullback R S M (firstMap R S s • z)) =
    s • firstModel R S M (flipPullback R S M z)
  exact (congrArg (firstModel R S M) h).trans
    (firstModel_second_smul R S M s (flipPullback R S M z))

@[simp]
theorem firstModel_symm_tmul (s : S) (m : (restrictScalars (algebraMap R S)).obj M) :
    (firstModel R S M).symm (s ⊗ₜ[R] m) =
      (1 ⊗ₜ[R] s) ⊗ₜ[S,firstMap R S] (show M from m) := by
  apply (firstModel R S M).injective
  erw [AddEquiv.apply_symm_apply]

@[simp]
theorem secondModel_symm_tmul (s : S) (m : (restrictScalars (algebraMap R S)).obj M) :
    (secondModel R S M).symm (s ⊗ₜ[R] m) =
      (s ⊗ₜ[R] 1) ⊗ₜ[S,secondMap R S] (show M from m) := by
  apply (secondModel R S M).injective
  erw [AddEquiv.apply_symm_apply]

/-- The inverse first model takes coefficient scalars to the second coordinate ring. -/
theorem firstModel_symm_smul (s : S)
    (z : S ⊗[R] (restrictScalars (algebraMap R S)).obj M) :
    (firstModel R S M).symm (s • z) =
      secondMap R S s • (firstModel R S M).symm z := by
  apply (firstModel R S M).injective
  rw [AddEquiv.apply_symm_apply, firstModel_second_smul, AddEquiv.apply_symm_apply]

/-- The two projection maps agree on the original base ring. -/
theorem projection_base_eq (r : R) :
    firstMap R S (algebraMap R S r) = secondMap R S (algebraMap R S r) := by
  change algebraMap R S r ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] algebraMap R S r
  simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels
