import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationCoordinates
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationCoordinateMap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationFixedMap

/-! # Multiplication Pullback Square -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationPullbackSquare

noncomputable section

/-! Pullback of a full line multiplication through a square of group and fixed coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {S : Scheme.{u}} {E F A B X Y : Over S} [GrpObj A] [GrpObj B]
  (p : E ⟶ A) (r : E ⟶ X) (p' : F ⟶ B) (r' : F ⟶ Y)
  (q : E ⟶ F) (f : A ⟶ B) [IsMonHom f] (g : X ⟶ Y)
  (hp : q ≫ p' = p ≫ f) (hr : q ≫ r' = r ≫ g)
  (L : Line.Bundles.LineBundle F.left) (D : FiberwiseMultiplication.Multiplication p' r' L)

/-- The genuine multiplication first pulls back to its two image coordinates. -/
def imageMultiplication : FiberwiseMultiplication.Multiplication (p ≫ f) (r ≫ g) (L.pullback q.left) :=
  MultiplicationCoordinates.congrCoordinates
    (FiberwiseMultiplicationPullback.pullbackMultiplication p' r' q L D) hp hr

/-- Refining both actual coordinates constructs the complete original-coordinate multiplication. -/
def multiplication : FiberwiseMultiplication.Multiplication p r (L.pullback q.left) :=
  MultiplicationFixedMap.restrictFixed p r g (L.pullback q.left)
    (MultiplicationCoordinateMap.restrictCoordinate p (r ≫ g) f (L.pullback q.left)
      (imageMultiplication p r p' r' q f g hp hr L D))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationPullbackSquare
