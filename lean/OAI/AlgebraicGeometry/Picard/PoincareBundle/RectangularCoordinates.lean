import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-! # Rectangular Coordinates -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularCoordinates

/-!
# Coordinates for descent through a product of two quotient maps
-/

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)

/-- The horizontal relation changes only the first coordinate, within one quotient fiber. -/
def Horizontal {T : C} (a b : T ⟶ A ⊗ X) : Prop :=
  a ≫ fst A X ≫ f = b ≫ fst A X ≫ f ∧ a ≫ snd A X = b ≫ snd A X

/-- The vertical relation changes only the second coordinate, within one quotient fiber. -/
def Vertical {T : C} (a b : T ⟶ A ⊗ X) : Prop :=
  a ≫ fst A X = b ≫ fst A X ∧ a ≫ snd A X ≫ g = b ≫ snd A X ≫ g

/-- First move horizontally from the source, then vertically to the target. -/
def middle {T : C} (a b : T ⟶ A ⊗ X) : T ⟶ A ⊗ X := lift (b ≫ fst A X) (a ≫ snd A X)

@[simp]
theorem middle_fst {T : C} (a b : T ⟶ A ⊗ X) : middle a b ≫ fst A X = b ≫ fst A X :=
  lift_fst _ _

@[simp]
theorem middle_snd {T : C} (a b : T ⟶ A ⊗ X) : middle a b ≫ snd A X = a ≫ snd A X :=
  lift_snd _ _

@[simp]
theorem middle_self {T : C} (a : T ⟶ A ⊗ X) : middle a a = a := lift_comp_fst_snd a

/-- The middle point commutes with arbitrary changes of test object. -/
theorem middle_naturality {T T' : C} (t : T' ⟶ T) (a b : T ⟶ A ⊗ X)
    (a' b' : T' ⟶ A ⊗ X) (ha : t ≫ a = a') (hb : t ≫ b = b') :
    t ≫ middle a b = middle a' b' := by
  dsimp only [middle]
  rw [comp_lift, ← Category.assoc, ← Category.assoc, ha, hb]

/-- Equality after the product quotient gives equality after its first-coordinate quotient. -/
theorem relation_fst {T : C} (a b : T ⟶ A ⊗ X) (h : a ≫ (f ⊗ₘ g) = b ≫ (f ⊗ₘ g)) :
    a ≫ fst A X ≫ f = b ≫ fst A X ≫ f := by
  have he := congrArg (fun t => t ≫ fst B Y) h
  simpa only [Category.assoc, tensorHom_fst] using he

/-- Equality after the product quotient gives equality after its second-coordinate quotient. -/
theorem relation_snd {T : C} (a b : T ⟶ A ⊗ X) (h : a ≫ (f ⊗ₘ g) = b ≫ (f ⊗ₘ g)) :
    a ≫ snd A X ≫ g = b ≫ snd A X ≫ g := by
  have he := congrArg (fun t => t ≫ snd B Y) h
  simpa only [Category.assoc, tensorHom_snd] using he

/-- The first half of the canonical rectangular path is horizontal. -/
theorem horizontal_middle {T : C} (a b : T ⟶ A ⊗ X) (h : a ≫ (f ⊗ₘ g) = b ≫ (f ⊗ₘ g)) :
    Horizontal f a (middle a b) := by
  constructor
  · simpa only [← Category.assoc, middle_fst] using relation_fst f g a b h
  · exact (middle_snd a b).symm

/-- The second half of the canonical rectangular path is vertical. -/
theorem vertical_middle {T : C} (a b : T ⟶ A ⊗ X) (h : a ≫ (f ⊗ₘ g) = b ≫ (f ⊗ₘ g)) :
    Vertical g (middle a b) b := by
  constructor
  · exact middle_fst a b
  · simpa only [← Category.assoc, middle_snd] using relation_snd f g a b h

/-- Horizontal movement between the two top middle points comes from the second quotient relation. -/
theorem horizontal_middles {T : C} (a b c : T ⟶ A ⊗ X)
    (h : b ≫ (f ⊗ₘ g) = c ≫ (f ⊗ₘ g)) : Horizontal f (middle a b) (middle a c) := by
  constructor
  · simpa only [← Category.assoc, middle_fst] using relation_fst f g b c h
  · rw [middle_snd, middle_snd]

/-- Vertical movement between the two right middle points comes from the first quotient relation. -/
theorem vertical_middles {T : C} (a b c : T ⟶ A ⊗ X)
    (h : a ≫ (f ⊗ₘ g) = b ≫ (f ⊗ₘ g)) : Vertical g (middle a c) (middle b c) := by
  constructor
  · rw [middle_fst, middle_fst]
  · simpa only [← Category.assoc, middle_snd] using relation_snd f g a b h

end OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularCoordinates
