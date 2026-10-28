import OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleSwitchNext

/-! # Cocycle Normalization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleNormalization

noncomputable section

/-!
# Diagonal and symmetry identities follow from invertible gluing and the cocycle
-/

open TensorProduct
open scoped TensorProduct

universe u

/-- In a braid relation, an involutive generator forces the other generator to be involutive. -/
theorem braid_involutive {X : Type*} (a b : X ≃ X) (hb : Function.Involutive b)
    (h : ∀ x, a (b (a x)) = b (a (b x))) : Function.Involutive a := by
  intro x
  apply a.injective.comp b.injective
  change a (b (a (a x))) = a (b x)
  rw [h (a x), h x, hb]

open OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentSwitch OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleSwitchNext

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type u} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

omit [IsScalarTower R S M] in
/-- The tensor cocycle forces transposition of the two factors to invert the gluing. -/
theorem switch_involutive (D : CocycleSwitchNext.CocycleSwitch R S M) : Function.Involutive D.switch := by
  let a := TensorProduct.congr (LinearEquiv.refl R S) D.switch
  let b := TensorProduct.leftComm R S S M
  have hb : Function.Involutive b := by
    have h : b.toLinearMap ∘ₗ b.toLinearMap = LinearMap.id :=
      TensorProduct.ext_threefold' (fun _ _ _ => rfl)
    exact LinearMap.congr_fun h
  have ha : Function.Involutive a := braid_involutive a.toEquiv b.toEquiv hb
    (fun z => LinearMap.congr_fun D.cocycle z)
  intro z
  have h := ha ((1 : S) ⊗ₜ[R] z)
  change (1 : S) ⊗ₜ[R] D.switch (D.switch z) = (1 : S) ⊗ₜ[R] z at h
  have hd := congrArg (DescentSwitch.diagonal R S (S ⊗[R] M)) h
  simpa only [DescentSwitch.diagonal_tmul, one_smul] using hd

theorem switch_secondScalar (D : CocycleSwitchNext.CocycleSwitch R S M) (s : S) (z : S ⊗[R] M) :
    D.switch (DescentSwitch.secondScalar (R := R) (M := M) s z) = s • D.switch z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul t m => exact D.second_smul s t m

/-- The coaction determines the original gluing on every pure tensor. -/
theorem switch_tmul (D : CocycleSwitchNext.CocycleSwitch R S M) (s : S) (m : M) :
    D.switch (s ⊗ₜ[R] m) = DescentSwitch.secondScalar (R := R) (M := M) s (D.coaction m) := by
  apply D.switch.injective
  rw [switch_involutive D, switch_secondScalar]
  change s ⊗ₜ[R] m = s • D.switch (D.switch (1 ⊗ₜ[R] m))
  rw [switch_involutive D]
  rw [smul_tmul', smul_eq_mul, mul_one]

theorem diagonal_secondScalar (s : S) (z : S ⊗[R] M) :
    DescentSwitch.diagonal R S M (DescentSwitch.secondScalar (R := R) (M := M) s z) = s • DescentSwitch.diagonal R S M z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul t m =>
      change t • (s • m) = s • (t • m)
      exact smul_comm t s m

/-- The diagonal compatibility is forced by invertible gluing and the cocycle. -/
theorem diagonal_switch (D : CocycleSwitchNext.CocycleSwitch R S M) (z : S ⊗[R] M) :
    DescentSwitch.diagonal R S M (D.switch z) = DescentSwitch.diagonal R S M z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s m => rw [switch_tmul, diagonal_secondScalar, D.counit, DescentSwitch.diagonal_tmul]

/-- An ordinary gluing cocycle supplies all the normalized descent-switch identities. -/
def toSwitch (D : CocycleSwitchNext.CocycleSwitch R S M) : DescentSwitch.SwitchDatum R S M where
  switch := D.switch
  second_smul := D.second_smul
  diagonal_switch := CocycleNormalization.diagonal_switch D
  involutive := switch_involutive D
  cocycle := D.cocycle

/-- The derived normalization retains the exact original coaction. -/
theorem toSwitch_coaction (D : CocycleSwitchNext.CocycleSwitch R S M) : (toSwitch D).coaction = D.coaction := rfl

/-- Coaction extraction loses none of the original gluing switch. -/
theorem switch_eq_of_coaction_eq (D E : CocycleSwitchNext.CocycleSwitch R S M) (h : D.coaction = E.coaction) :
    D.switch = E.switch :=
  DescentSwitch.SwitchDatum.switch_eq_of_coaction_eq (toSwitch D) (toSwitch E) h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleNormalization
