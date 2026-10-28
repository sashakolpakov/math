import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! # Descent Switch -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentSwitch

noncomputable section

/-!
# Extracting a coaction from an algebraic descent switch for PoincareBundle

A descent switch exchanges the two S-actions on `S ⊗[R] M`.
The diagonal identity and the three-factor cocycle imply the counit
and coassociativity equations for `m ↦ switch (1 ⊗ m)`.
-/

open TensorProduct
open scoped TensorProduct

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : Type u) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- Restrict an extended module to the diagonal. -/
def diagonal : S ⊗[R] M →ₗ[R] M :=
  TensorProduct.lift (Algebra.lsmul R R M).toLinearMap

@[simp]
theorem diagonal_tmul (s : S) (m : M) : diagonal R S M (s ⊗ₜ[R] m) = s • m := rfl

/-- Insert a unit scalar into the scalar extension. -/
def unitMap : M →ₗ[R] S ⊗[R] M := TensorProduct.mk R S M 1

/-- Extend a switch to the last two factors of a three-factor tensor product. -/
def nextSwitch (τ : S ⊗[R] M ≃ₗ[R] S ⊗[R] M) :
    S ⊗[R] (S ⊗[R] M) →ₗ[R] S ⊗[R] (S ⊗[R] M) :=
  TensorProduct.map LinearMap.id τ.toLinearMap

/-- The ordinary descent identities, expressed by exchanging tensor factors. -/
structure SwitchDatum where
  switch : S ⊗[R] M ≃ₗ[R] S ⊗[R] M
  second_smul : ∀ (s t : S) (m : M),
    switch (t ⊗ₜ[R] (s • m)) = s • switch (t ⊗ₜ[R] m)
  diagonal_switch : ∀ z, diagonal R S M (switch z) = diagonal R S M z
  involutive : ∀ z, switch (switch z) = z
  cocycle :
    nextSwitch R S M switch ∘ₗ (TensorProduct.leftComm R S S M).toLinearMap ∘ₗ
        nextSwitch R S M switch =
      (TensorProduct.leftComm R S S M).toLinearMap ∘ₗ nextSwitch R S M switch ∘ₗ
        (TensorProduct.leftComm R S S M).toLinearMap

variable {R S M}

/-- The coaction is obtained by applying the switch to the unit tensor. -/
def SwitchDatum.coaction (D : SwitchDatum R S M) : M →ₗ[S] S ⊗[R] M where
  toFun m := D.switch (1 ⊗ₜ[R] m)
  map_add' x y := by rw [tmul_add, map_add]
  map_smul' s m := D.second_smul s 1 m

@[simp]
theorem SwitchDatum.coaction_apply (D : SwitchDatum R S M) (m : M) :
    D.coaction m = D.switch (1 ⊗ₜ[R] m) := rfl

/-- The diagonal identity is the coaction counit equation. -/
theorem SwitchDatum.counit (D : SwitchDatum R S M) (m : M) :
    diagonal R S M (D.coaction m) = m := by
  rw [SwitchDatum.coaction_apply, D.diagonal_switch, diagonal_tmul, one_smul]

omit [Module S M] [IsScalarTower R S M] in
/-- Swapping a leading unit inserts the unit in the middle tensor factor. -/
theorem swap_unit (z : S ⊗[R] M) :
    TensorProduct.leftComm R S S M (1 ⊗ₜ[R] z) =
      TensorProduct.map (LinearMap.id : S →ₗ[R] S) (unitMap R S M) z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | tmul s m => rfl

/-- Switching after that insertion applies the extracted coaction to the module factor. -/
theorem SwitchDatum.next_swap_unit (D : SwitchDatum R S M) (z : S ⊗[R] M) :
    nextSwitch R S M D.switch (TensorProduct.leftComm R S S M (1 ⊗ₜ[R] z)) =
      TensorProduct.map (LinearMap.id : S →ₗ[R] S) (D.coaction.restrictScalars R) z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | tmul s m => rfl

/-- The three-factor descent cocycle gives coassociativity. -/
theorem SwitchDatum.coassoc (D : SwitchDatum R S M) (m : M) :
    TensorProduct.map (LinearMap.id : S →ₗ[R] S) (D.coaction.restrictScalars R) (D.coaction m) =
      TensorProduct.map (LinearMap.id : S →ₗ[R] S) (unitMap R S M) (D.coaction m) := by
  have h := LinearMap.congr_fun D.cocycle ((1 : S) ⊗ₜ[R] ((1 : S) ⊗ₜ[R] m))
  change nextSwitch R S M D.switch
      (TensorProduct.leftComm R S S M (1 ⊗ₜ[R] D.coaction m)) =
    TensorProduct.leftComm R S S M (1 ⊗ₜ[R] D.coaction m) at h
  rw [D.next_swap_unit, swap_unit] at h
  exact h

/-- Scalar multiplication on the module factor of the tensor product. -/
def secondScalar (s : S) : S ⊗[R] M →ₗ[R] S ⊗[R] M :=
  TensorProduct.map LinearMap.id (Algebra.lsmul R R M s)

/-- The switch exchanges the module-factor and coefficient-factor scalar actions. -/
theorem SwitchDatum.switch_secondScalar (D : SwitchDatum R S M) (s : S)
    (z : S ⊗[R] M) :
    D.switch (secondScalar (R := R) (M := M) s z) = s • D.switch z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul t m => exact D.second_smul s t m

/-- The original switch is recovered on pure tensors from its extracted coaction. -/
theorem SwitchDatum.switch_tmul (D : SwitchDatum R S M) (s : S) (m : M) :
    D.switch (s ⊗ₜ[R] m) = secondScalar (R := R) (M := M) s (D.coaction m) := by
  apply D.switch.injective
  rw [D.involutive, D.switch_secondScalar, SwitchDatum.coaction_apply, D.involutive]
  rw [smul_tmul', smul_eq_mul, mul_one]

/-- Passing to the extracted coaction loses no descent-switch information. -/
theorem SwitchDatum.switch_eq_of_coaction_eq (D E : SwitchDatum R S M)
    (h : D.coaction = E.coaction) : D.switch = E.switch := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext
  ext s m
  change D.switch (s ⊗ₜ[R] m) = E.switch (s ⊗ₜ[R] m)
  rw [D.switch_tmul, E.switch_tmul, h]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentSwitch
