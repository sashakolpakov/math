import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentSwitch

/-! # Cocycle Switch Next -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleSwitchNext

noncomputable section

/-!
# A gluing cocycle forces the coaction counit law

Invertibility of the gluing makes the extracted coaction injective. Its
coassociativity then implies the counit equation, without a separate
diagonal or transposition hypothesis.
-/

open TensorProduct
open scoped TensorProduct

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentSwitch

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : Type u) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- The switch and cocycle supplied by an actual invertible Čech gluing map. -/
structure CocycleSwitch where
  switch : S ⊗[R] M ≃ₗ[R] S ⊗[R] M
  second_smul : ∀ (s t : S) (m : M), switch (t ⊗ₜ[R] (s • m)) = s • switch (t ⊗ₜ[R] m)
  cocycle :
    DescentSwitch.nextSwitch R S M switch ∘ₗ (TensorProduct.leftComm R S S M).toLinearMap ∘ₗ
        DescentSwitch.nextSwitch R S M switch =
      (TensorProduct.leftComm R S S M).toLinearMap ∘ₗ DescentSwitch.nextSwitch R S M switch ∘ₗ
        (TensorProduct.leftComm R S S M).toLinearMap

variable {R S M}

def CocycleSwitch.coaction (D : CocycleSwitch R S M) : M →ₗ[S] S ⊗[R] M where
  toFun m := D.switch (1 ⊗ₜ[R] m)
  map_add' x y := by rw [tmul_add, map_add]
  map_smul' s m := D.second_smul s 1 m

/-- Invertibility of the gluing implies injectivity of the extracted coaction. -/
theorem CocycleSwitch.coaction_injective (D : CocycleSwitch R S M) :
    Function.Injective D.coaction := by
  intro x y h
  have ht : (1 : S) ⊗ₜ[R] x = (1 : S) ⊗ₜ[R] y := D.switch.injective h
  have hd := congrArg (DescentSwitch.diagonal R S M) ht
  simpa only [DescentSwitch.diagonal_tmul, one_smul] using hd

theorem CocycleSwitch.next_swap_unit (D : CocycleSwitch R S M) (z : S ⊗[R] M) :
    DescentSwitch.nextSwitch R S M D.switch (TensorProduct.leftComm R S S M (1 ⊗ₜ[R] z)) =
      TensorProduct.map (LinearMap.id : S →ₗ[R] S) (D.coaction.restrictScalars R) z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | tmul s m => rfl

/-- The actual gluing cocycle gives coassociativity before any counit is assumed. -/
theorem CocycleSwitch.coassoc (D : CocycleSwitch R S M) (m : M) :
    TensorProduct.map (LinearMap.id : S →ₗ[R] S) (D.coaction.restrictScalars R) (D.coaction m) =
      TensorProduct.map (LinearMap.id : S →ₗ[R] S) (DescentSwitch.unitMap R S M) (D.coaction m) := by
  have h := LinearMap.congr_fun D.cocycle ((1 : S) ⊗ₜ[R] ((1 : S) ⊗ₜ[R] m))
  change DescentSwitch.nextSwitch R S M D.switch
      (TensorProduct.leftComm R S S M (1 ⊗ₜ[R] D.coaction m)) =
    TensorProduct.leftComm R S S M (1 ⊗ₜ[R] D.coaction m) at h
  rw [D.next_swap_unit, DescentSwitch.swap_unit] at h
  exact h

/-- Multiplication is natural with respect to the extracted S-linear coaction. -/
theorem CocycleSwitch.diagonal_map (D : CocycleSwitch R S M) (z : S ⊗[R] M) :
    DescentSwitch.diagonal R S (S ⊗[R] M)
        (TensorProduct.map (LinearMap.id : S →ₗ[R] S) (D.coaction.restrictScalars R) z) =
      D.coaction (DescentSwitch.diagonal R S M z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s m =>
      change s • D.coaction m = D.coaction (s • m)
      exact (D.coaction.map_smul s m).symm

omit [Module S M] [IsScalarTower R S M] in
theorem diagonal_insert (z : S ⊗[R] M) :
    DescentSwitch.diagonal R S (S ⊗[R] M)
      (TensorProduct.map (LinearMap.id : S →ₗ[R] S) (DescentSwitch.unitMap R S M) z) = z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s m =>
      change s • ((1 : S) ⊗ₜ[R] m) = s ⊗ₜ[R] m
      rw [smul_tmul', smul_eq_mul, mul_one]

/-- The counit law follows from the cocycle and invertibility of the gluing. -/
theorem CocycleSwitch.counit (D : CocycleSwitch R S M) (m : M) :
    DescentSwitch.diagonal R S M (D.coaction m) = m := by
  apply D.coaction_injective
  rw [← D.diagonal_map, D.coassoc, diagonal_insert]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleSwitchNext
