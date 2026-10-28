import Mathlib

/-! # Coordinate Blocks -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CoordinateBlocks

noncomputable section

/-! A coordinate idempotent in a split product ring has one free
coordinate in each copy of the coefficient module. These are actual
fixed-point equivalences, suitable for cardinal computations. -/

open scoped Classical

def scalarFixedEquiv {R M P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (e : M ≃ₗ[R] P) (a : R) :
    {x : M // a • x = x} ≃ {x : P // a • x = x} where
  toFun x := ⟨e x.val, by rw [← e.map_smul, x.property]⟩
  invFun x := ⟨e.symm x.val, by rw [← e.symm.map_smul, x.property]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)

def coordinateBlockEquiv {A B I T : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* (T → B)) (a : A) (t : T) (ha : e a = Pi.single t 1) :
    {x : I → A // ∀ i, a * x i = x i} ≃ (I → B) where
  toFun x i := e (x.val i) t
  invFun y := ⟨fun i => e.symm (Pi.single t (y i)), by
    intro i
    apply e.injective
    rw [map_mul, ha, e.apply_symm_apply]
    ext u
    by_cases hu : u = t
    · subst u
      simp
    · simp [Pi.single_eq_of_ne hu]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    apply e.injective
    rw [e.apply_symm_apply]
    ext u
    by_cases hu : u = t
    · subst u
      simp
    · have hx := congrFun (congrArg e (x.property i)) u
      rw [map_mul, ha] at hx
      simpa [Pi.single_eq_of_ne hu] using hx
  right_inv y := by
    funext i
    simp

theorem coordinateBlock_card {A B I T : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* (T → B)) (a : A) (t : T) (ha : e a = Pi.single t 1) :
    Nat.card {x : I → A // ∀ i, a * x i = x i} = Nat.card (I → B) :=
  Nat.card_congr (coordinateBlockEquiv e a t ha)

def quotientCoordinateBlockEquiv {R B I T : Type*} [CommRing R] [CommRing B]
    (J : Ideal R) (e : (R ⧸ J) ≃+* (T → B)) (a : R) (t : T)
    (ha : e (Ideal.Quotient.mk J a) = Pi.single t 1) :
    {x : I → R ⧸ J // a • x = x} ≃ (I → B) :=
  (Equiv.subtypeEquivRight (fun x => show a • x = x ↔
      ∀ i, Ideal.Quotient.mk J a * x i = x i from by
    constructor
    · intro h i
      exact congrFun h i
    · intro h
      exact funext h)).trans
    (coordinateBlockEquiv e (Ideal.Quotient.mk J a) t ha)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CoordinateBlocks
