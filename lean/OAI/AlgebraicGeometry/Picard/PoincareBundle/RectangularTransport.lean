import OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularCoordinates
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

/-! # Rectangular Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularTransport

noncomputable section

/-!
# Commuting coordinate transports give descent through a product quotient

Only the separate horizontal and vertical cocycles are input. The full product cocycle and the
ordinary descent datum are constructed from their commuting squares.
-/

open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'

open OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularCoordinates

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) (L : F.obj (.mk (op (A ⊗ X))))

/-- The actual pseudofunctor fiber at a test point of the product. -/
abbrev pointObject {T : C} (a : T ⟶ A ⊗ X) : F.obj (.mk (op T)) :=
  (F.map a.op.toLoc).toFunctor.obj L

/-- Separate coordinate transport laws, before imposing any interchange condition. -/
structure AxisData where
  horizontal {T : C} (a b : T ⟶ A ⊗ X) (h : RectangularCoordinates.Horizontal f a b) :
    pointObject F L a ⟶ pointObject F L b
  vertical {T : C} (a b : T ⟶ A ⊗ X) (h : RectangularCoordinates.Vertical g a b) :
    pointObject F L a ⟶ pointObject F L b
  horizontal_self {T : C} (a : T ⟶ A ⊗ X) (h : RectangularCoordinates.Horizontal f a a) : horizontal a a h = 𝟙 _
  vertical_self {T : C} (a : T ⟶ A ⊗ X) (h : RectangularCoordinates.Vertical g a a) : vertical a a h = 𝟙 _
  horizontal_comp {T : C} (a b c : T ⟶ A ⊗ X)
      (hab : RectangularCoordinates.Horizontal f a b) (hbc : RectangularCoordinates.Horizontal f b c) (hac : RectangularCoordinates.Horizontal f a c) :
    horizontal a b hab ≫ horizontal b c hbc = horizontal a c hac
  vertical_comp {T : C} (a b c : T ⟶ A ⊗ X)
      (hab : RectangularCoordinates.Vertical g a b) (hbc : RectangularCoordinates.Vertical g b c) (hac : RectangularCoordinates.Vertical g a c) :
    vertical a b hab ≫ vertical b c hbc = vertical a c hac
  horizontal_pullback {T T' : C} (t : T' ⟶ T) (a b : T ⟶ A ⊗ X) (h : RectangularCoordinates.Horizontal f a b)
      (a' b' : T' ⟶ A ⊗ X) (h' : RectangularCoordinates.Horizontal f a' b') (ha : t ≫ a = a') (hb : t ≫ b = b') :
    pullHom (horizontal a b h) t a' b' ha hb = horizontal a' b' h'
  vertical_pullback {T T' : C} (t : T' ⟶ T) (a b : T ⟶ A ⊗ X) (h : RectangularCoordinates.Vertical g a b)
      (a' b' : T' ⟶ A ⊗ X) (h' : RectangularCoordinates.Vertical g a' b') (ha : t ≫ a = a') (hb : t ≫ b = b') :
    pullHom (vertical a b h) t a' b' ha hb = vertical a' b' h'

variable (D : AxisData f g F L)

/-- The two already-defined coordinate transports commute around every actual rectangle. -/
def Commutes : Prop := ∀ (T : C) (a b c d : T ⟶ A ⊗ X)
  (hab : RectangularCoordinates.Horizontal f a b) (hac : RectangularCoordinates.Vertical g a c) (hbd : RectangularCoordinates.Vertical g b d) (hcd : RectangularCoordinates.Horizontal f c d),
  D.horizontal a b hab ≫ D.vertical b d hbd = D.vertical a c hac ≫ D.horizontal c d hcd

/-- The canonical product transport first changes the first coordinate, then the second. -/
def total {T : C} (a b : T ⟶ A ⊗ X) (h : a ≫ (f ⊗ₘ g) = b ≫ (f ⊗ₘ g)) :
    pointObject F L a ⟶ pointObject F L b :=
  D.horizontal a (RectangularCoordinates.middle a b) (RectangularCoordinates.horizontal_middle f g a b h) ≫
    D.vertical (RectangularCoordinates.middle a b) b (RectangularCoordinates.vertical_middle f g a b h)

/-- The derived product transport satisfies its unit law. -/
theorem total_self {T : C} (a : T ⟶ A ⊗ X) (h : a ≫ (f ⊗ₘ g) = a ≫ (f ⊗ₘ g)) :
    total f g F L D a a h = 𝟙 _ := by
  have he (m : T ⟶ A ⊗ X) (hm : m = a) (hh : RectangularCoordinates.Horizontal f a m) (hv : RectangularCoordinates.Vertical g m a) :
      D.horizontal a m hh ≫ D.vertical m a hv = 𝟙 _ := by
    subst m
    rw [D.horizontal_self, D.vertical_self, Category.id_comp]
  exact he (RectangularCoordinates.middle a a) (RectangularCoordinates.middle_self a) _ _

variable (hc : Commutes f g F L D)

include hc in
/-- A commuting rectangle combines the two separate cocycles into the full product cocycle. -/
theorem total_comp {T : C} (a b c : T ⟶ A ⊗ X)
    (hab : a ≫ (f ⊗ₘ g) = b ≫ (f ⊗ₘ g)) (hbc : b ≫ (f ⊗ₘ g) = c ≫ (f ⊗ₘ g))
    (hac : a ≫ (f ⊗ₘ g) = c ≫ (f ⊗ₘ g)) :
    total f g F L D a b hab ≫ total f g F L D b c hbc = total f g F L D a c hac := by
  have hs := hc T (RectangularCoordinates.middle a b) (RectangularCoordinates.middle a c) b (RectangularCoordinates.middle b c)
    (RectangularCoordinates.horizontal_middles f g a b c hbc) (RectangularCoordinates.vertical_middle f g a b hab)
    (RectangularCoordinates.vertical_middles f g a b c hab) (RectangularCoordinates.horizontal_middle f g b c hbc)
  unfold total
  simp only [Category.assoc]
  slice_lhs 2 3 => exact hs.symm
  slice_lhs 1 2 =>
    exact D.horizontal_comp a (RectangularCoordinates.middle a b) (RectangularCoordinates.middle a c)
      (RectangularCoordinates.horizontal_middle f g a b hab) (RectangularCoordinates.horizontal_middles f g a b c hbc)
      (RectangularCoordinates.horizontal_middle f g a c hac)
  rw [Category.assoc, D.vertical_comp]

/-- Both coordinate transports and the chosen middle point commute with change of test object. -/
theorem total_pullback {T T' : C} (t : T' ⟶ T) (a b : T ⟶ A ⊗ X)
    (h : a ≫ (f ⊗ₘ g) = b ≫ (f ⊗ₘ g)) (a' b' : T' ⟶ A ⊗ X)
    (h' : a' ≫ (f ⊗ₘ g) = b' ≫ (f ⊗ₘ g)) (ha : t ≫ a = a') (hb : t ≫ b = b') :
    pullHom (total f g F L D a b h) t a' b' ha hb = total f g F L D a' b' h' := by
  have hm := RectangularCoordinates.middle_naturality t a b a' b' ha hb
  unfold total
  rw [PullHom.pullHom_comp _ _ t a' (RectangularCoordinates.middle a' b') b' ha hm hb,
    D.horizontal_pullback t a (RectangularCoordinates.middle a b) _ a' (RectangularCoordinates.middle a' b')
      (RectangularCoordinates.horizontal_middle f g a' b' h') ha hm,
    D.vertical_pullback t (RectangularCoordinates.middle a b) b _ (RectangularCoordinates.middle a' b') b'
      (RectangularCoordinates.vertical_middle f g a' b' h') hm hb]

/-- The derived transport supplies ordinary descent data for the actual product quotient. -/
def toDescentData : F.DescentData (fun (_ : PUnit.{1}) => f ⊗ₘ g) where
  obj _ := L
  hom _T _q _i _j a b ha hb := total f g F L D a b (ha.trans hb.symm)
  pullHom_hom _T' _T t _q _q' _hq _i _j a b ha hb a' b' hta htb :=
    total_pullback f g F L D t a b (ha.trans hb.symm) a' b' _ hta htb
  hom_self _T _q _i a ha := total_self f g F L D a (ha.trans ha.symm)
  hom_comp _T _q _i _j _k a b c ha hb hcc :=
    total_comp f g F L D hc a b c (ha.trans hb.symm) (hb.trans hcc.symm) (ha.trans hcc.symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularTransport
