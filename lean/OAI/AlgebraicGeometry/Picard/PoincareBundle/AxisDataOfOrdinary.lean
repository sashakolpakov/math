import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.QuotientTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularTransport

/-! # Axis Data Of Ordinary -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.AxisDataOfOrdinary.Ordinary

noncomputable section

/-!
# Construct coordinate transports from two actual one-coordinate ordinary descent data
-/

open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u v u' v'

open OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularCoordinates OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.QuotientTransport

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)

/-- A horizontal rectangle edge is precisely a relation for the first product cover. -/
theorem horizontal_relation {T : C} (x y : T ⟶ A ⊗ X) (h : RectangularCoordinates.Horizontal f x y) :
    x ≫ (f ⊗ₘ 𝟙 X) = y ≫ (f ⊗ₘ 𝟙 X) := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [Category.assoc, tensorHom_fst] using h.1
  · simpa only [Category.assoc, tensorHom_snd, Category.comp_id] using h.2

/-- A vertical rectangle edge is precisely a relation for the second product cover. -/
theorem vertical_relation {T : C} (x y : T ⟶ A ⊗ X) (h : RectangularCoordinates.Vertical g x y) :
    x ≫ (𝟙 A ⊗ₘ g) = y ≫ (𝟙 A ⊗ₘ g) := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [Category.assoc, tensorHom_fst, Category.comp_id] using h.1
  · simpa only [Category.assoc, tensorHom_snd] using h.2

variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) (L : F.obj (.mk (op (A ⊗ X))))
  (Dh : F.DescentData (fun (_ : PUnit.{1}) => f ⊗ₘ 𝟙 X))
  (Dv : F.DescentData (fun (_ : PUnit.{1}) => 𝟙 A ⊗ₘ g))
  (eh : L ≅ Dh.obj PUnit.unit) (ev : L ≅ Dv.obj PUnit.unit)

/-- Put the first ordinary datum on the fixed original object. -/
def horizontalDatum : F.DescentData (fun (_ : PUnit.{1}) => f ⊗ₘ 𝟙 X) :=
  Ordinary.DescentObjectIso.ofIso F (f ⊗ₘ 𝟙 X) Dh L eh

/-- Put the second ordinary datum on the same original object. -/
def verticalDatum : F.DescentData (fun (_ : PUnit.{1}) => 𝟙 A ⊗ₘ g) :=
  Ordinary.DescentObjectIso.ofIso F (𝟙 A ⊗ₘ g) Dv L ev

/-- Horizontal transport is the genuine ordinary gluing for the first quotient cover. -/
def horizontal {T : C} (x y : T ⟶ A ⊗ X) (h : RectangularCoordinates.Horizontal f x y) :
    RectangularTransport.pointObject F L x ⟶ RectangularTransport.pointObject F L y :=
  Ordinary.QuotientTransport.transport (f ⊗ₘ 𝟙 X) (horizontalDatum f F L Dh eh) x y (horizontal_relation f x y h)

/-- Vertical transport is the genuine ordinary gluing for the second quotient cover. -/
def vertical {T : C} (x y : T ⟶ A ⊗ X) (h : RectangularCoordinates.Vertical g x y) :
    RectangularTransport.pointObject F L x ⟶ RectangularTransport.pointObject F L y :=
  Ordinary.QuotientTransport.transport (𝟙 A ⊗ₘ g) (verticalDatum g F L Dv ev) x y (vertical_relation g x y h)

/-- The two ordinary data construct both coordinate cocycles on the original object. -/
def toAxisData : RectangularTransport.AxisData f g F L where
  horizontal := fun {_T} x y h => Ordinary.horizontal f F L Dh eh x y h
  vertical := fun {_T} x y h => Ordinary.vertical g F L Dv ev x y h
  horizontal_self := fun {_T} x h =>
    Ordinary.QuotientTransport.transport_self (f ⊗ₘ 𝟙 X) (horizontalDatum f F L Dh eh) x (horizontal_relation f x x h)
  vertical_self := fun {_T} x h =>
    Ordinary.QuotientTransport.transport_self (𝟙 A ⊗ₘ g) (verticalDatum g F L Dv ev) x (vertical_relation g x x h)
  horizontal_comp := fun {_T} x y z hxy hyz hxz =>
    Ordinary.QuotientTransport.transport_comp (f ⊗ₘ 𝟙 X) (horizontalDatum f F L Dh eh) x y z
      (horizontal_relation f x y hxy) (horizontal_relation f y z hyz) (horizontal_relation f x z hxz)
  vertical_comp := fun {_T} x y z hxy hyz hxz =>
    Ordinary.QuotientTransport.transport_comp (𝟙 A ⊗ₘ g) (verticalDatum g F L Dv ev) x y z
      (vertical_relation g x y hxy) (vertical_relation g y z hyz) (vertical_relation g x z hxz)
  horizontal_pullback := fun {_T _T'} t x y h x' y' h' hx hy =>
    Ordinary.QuotientTransport.transport_pullback (f ⊗ₘ 𝟙 X) (horizontalDatum f F L Dh eh) t x y (horizontal_relation f x y h)
      x' y' (horizontal_relation f x' y' h') hx hy
  vertical_pullback := fun {_T _T'} t x y h x' y' h' hx hy =>
    Ordinary.QuotientTransport.transport_pullback (𝟙 A ⊗ₘ g) (verticalDatum g F L Dv ev) t x y (vertical_relation g x y h)
      x' y' (vertical_relation g x' y' h') hx hy

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.AxisDataOfOrdinary.Ordinary
