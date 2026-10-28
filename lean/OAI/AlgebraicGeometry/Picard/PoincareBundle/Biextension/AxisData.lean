import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseQuotientTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularTransport

/-! # Axis Data -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData

noncomputable section

/-!
# The two actual biextension coordinate actions constructed from their kernel frames
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseQuotientTransport OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularCoordinates
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {A B X Y : Over S}

/-- Replace the first coordinate of the original product. -/
def replaceFirst : A ⊗ (A ⊗ X) ⟶ A ⊗ X :=
  lift (fst A (A ⊗ X)) (snd A (A ⊗ X) ≫ snd A X)

theorem replaceFirst_group : replaceFirst (A := A) (X := X) ≫ fst A X = fst A (A ⊗ X) :=
  lift_fst _ _

theorem replaceFirst_base : replaceFirst (A := A) (X := X) ≫ snd A X = snd A (A ⊗ X) ≫ snd A X :=
  lift_snd _ _

/-- Replace the second coordinate while keeping the original underlying product. -/
def replaceSecond : X ⊗ (A ⊗ X) ⟶ A ⊗ X :=
  lift (snd X (A ⊗ X) ≫ fst A X) (fst X (A ⊗ X))

theorem replaceSecond_group : replaceSecond (A := A) (X := X) ≫ snd A X = fst X (A ⊗ X) :=
  lift_snd _ _

theorem replaceSecond_base : replaceSecond (A := A) (X := X) ≫ fst A X = snd X (A ⊗ X) ≫ fst A X :=
  lift_fst _ _

/-- The horizontal quotient relation has the form used by the constructed coordinate transport. -/
theorem horizontalRelation (f : A ⟶ B) {T : Over S} (x y : T ⟶ A ⊗ X) (h : RectangularCoordinates.Horizontal f x y) :
    FiberwiseQuotientTransport.Relation (fst A X) (snd A X) f x y :=
  ⟨by simpa only [Category.assoc] using h.1, h.2⟩

/-- The vertical quotient relation has the form used by the same coordinate construction. -/
theorem verticalRelation (g : X ⟶ Y) {T : Over S} (x y : T ⟶ A ⊗ X) (h : RectangularCoordinates.Vertical g x y) :
    FiberwiseQuotientTransport.Relation (snd A X) (fst A X) g x y :=
  ⟨by simpa only [Category.assoc] using h.2, h.1⟩

variable [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- The first-coordinate quotient transport is an actual sheaf map built from multiplication. -/
def horizontal {T : Over S} (x y : T ⟶ A ⊗ X) (h : RectangularCoordinates.Horizontal f x y) :
    Line.Fibers.fiber L x ⟶ Line.Fibers.fiber L y :=
  FiberwiseQuotientTransport.transport (fst A X) (snd A X) f replaceFirst replaceFirst_group replaceFirst_base L Dh Kh
    x y (horizontalRelation f x y h)

/-- The second-coordinate quotient transport is an actual sheaf map on the same original line. -/
def vertical {T : Over S} (x y : T ⟶ A ⊗ X) (h : RectangularCoordinates.Vertical g x y) :
    Line.Fibers.fiber L x ⟶ Line.Fibers.fiber L y :=
  FiberwiseQuotientTransport.transport (snd A X) (fst A X) g replaceSecond replaceSecond_group replaceSecond_base L Dv Kv
    x y (verticalRelation g x y h)

/-- Both separate action cocycles and their native pullback laws are derived from the genuine products. -/
def toAxisData : RectangularTransport.AxisData f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf where
  horizontal := fun {_T} x y h => AxisData.horizontal f L Dh Kh x y h
  vertical := fun {_T} x y h => AxisData.vertical g L Dv Kv x y h
  horizontal_self := fun {_T} x h =>
    FiberwiseQuotientTransport.transport_self (fst A X) (snd A X) f replaceFirst replaceFirst_group replaceFirst_base L Dh Kh
      x (horizontalRelation f x x h)
  vertical_self := fun {_T} x h =>
    FiberwiseQuotientTransport.transport_self (snd A X) (fst A X) g replaceSecond replaceSecond_group replaceSecond_base L Dv Kv
      x (verticalRelation g x x h)
  horizontal_comp := fun {_T} x y z hxy hyz hxz =>
    FiberwiseQuotientTransport.transport_comp (fst A X) (snd A X) f replaceFirst replaceFirst_group replaceFirst_base L Dh Kh
      x y z (horizontalRelation f x y hxy) (horizontalRelation f y z hyz) (horizontalRelation f x z hxz)
  vertical_comp := fun {_T} x y z hxy hyz hxz =>
    FiberwiseQuotientTransport.transport_comp (snd A X) (fst A X) g replaceSecond replaceSecond_group replaceSecond_base L Dv Kv
      x y z (verticalRelation g x y hxy) (verticalRelation g y z hyz) (verticalRelation g x z hxz)
  horizontal_pullback := fun {_T _T'} t x y h x' y' h' hx hy =>
    FiberwiseQuotientTransport.transport_pullback (fst A X) (snd A X) f replaceFirst replaceFirst_group replaceFirst_base L Dh Kh
      t x y (horizontalRelation f x y h) x' y' (horizontalRelation f x' y' h') hx hy
  vertical_pullback := fun {_T _T'} t x y h x' y' h' hx hy =>
    FiberwiseQuotientTransport.transport_pullback (snd A X) (fst A X) g replaceSecond replaceSecond_group replaceSecond_base L Dv Kv
      t x y (verticalRelation g x y h) x' y' (verticalRelation g x' y' h') hx hy

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData
