import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

/-! # Multiplication Coordinates -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationCoordinates

noncomputable section

/-!
# Equality of actual coordinates preserves the multiplication and its neutral-frame normalization
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {S : Scheme.{u}} {E A X : Over S} [GrpObj A]
  {p p' : E ⟶ A} {r r' : E ⟶ X} {L : Line.Bundles.LineBundle E.left}

/-- The ordinary neutral-fiber multiplication equation, independent of any subgroup or quotient. -/
def NeutralProducts (D : FiberwiseMultiplication.Multiplication p r L) : Prop := ∀ (T : Over S) (a b c : T ⟶ E)
  (ha : a ≫ p = 1) (hb : b ≫ p = 1) (hc : c ≫ p = 1) (h : FiberwiseMultiplication.ProductRel p r a b c) (U : T.left.Opens),
  (D.product a b c h).app U ((D.unitFrame a ha).hom.app U (1 : Γ(T.left, U)))
    ((D.unitFrame b hb).hom.app U (1 : Γ(T.left, U))) = (D.unitFrame c hc).hom.app U (1 : Γ(T.left, U))

/-- Present the same actual multiplication in equal group and fixed coordinates. -/
def congrCoordinates (D : FiberwiseMultiplication.Multiplication p r L) (hp : p = p') (hr : r = r') : FiberwiseMultiplication.Multiplication p' r' L :=
  hp ▸ hr ▸ D

/-- Equality of the actual coordinate maps retains the normalized neutral-fiber product law. -/
theorem congrCoordinates_neutral (D : FiberwiseMultiplication.Multiplication p r L) (hp : p = p') (hr : r = r')
    (h : NeutralProducts D) : NeutralProducts (congrCoordinates D hp hr) := by
  cases hp
  cases hr
  exact h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationCoordinates
