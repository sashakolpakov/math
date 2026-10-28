import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationCoordinateMap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationFixedMap

/-! # Multiplication Restriction Commutes -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationRestrictionCommutes

/-! Refining the group and fixed coordinates in either order gives the same actual multiplication. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {S : Scheme.{u}} {E A B X Y : Over S} [GrpObj A] [GrpObj B]
  (p : E ⟶ A) (r : E ⟶ X) (f : A ⟶ B) [IsMonHom f] (g : X ⟶ Y)
  (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication (p ≫ f) (r ≫ g) L)

/-- Both orders retain exactly the same products and units; the relation witnesses are proofs. -/
theorem restrict_commutes :
    MultiplicationCoordinateMap.restrictCoordinate p r f L
      (MultiplicationFixedMap.restrictFixed (p ≫ f) r g L D) =
    MultiplicationFixedMap.restrictFixed p r g L
      (MultiplicationCoordinateMap.restrictCoordinate p (r ≫ g) f L D) := rfl

end OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationRestrictionCommutes
