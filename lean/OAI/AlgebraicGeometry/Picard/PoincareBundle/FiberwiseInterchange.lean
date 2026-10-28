import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.InterchangeTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationCoordinates
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationCoordinateMap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationFixedMap

/-! # Fiberwise Interchange -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseInterchange

noncomputable section

/-!
# Geometric pullback and coordinate restriction of genuine biextension interchange
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear

variable {S : Scheme.{u}} {E A X K : Over S} [GrpObj A] [GrpObj X]
  {p : E ⟶ A} {r : E ⟶ X} {L : Line.Bundles.LineBundle E.left}

/-- Interchange for two genuine line products in specified actual coordinates. -/
def Interchange (Dh : FiberwiseMultiplication.Multiplication p r L) (Dv : FiberwiseMultiplication.Multiplication r p L) : Prop :=
  ∀ (T : Over S) (c a b x a' b' y z w : T ⟶ E)
    (hax : FiberwiseMultiplication.ProductRel p r a x y) (hbx : FiberwiseMultiplication.ProductRel r p b x z)
    (hcb : FiberwiseMultiplication.ProductRel p r c b b') (hca : FiberwiseMultiplication.ProductRel r p c a a')
    (hby : FiberwiseMultiplication.ProductRel r p b' y w) (haz : FiberwiseMultiplication.ProductRel p r a' z w)
    (U : T.left.Opens) (sc : Γ(Line.Fibers.fiber L c, U)) (sa : Γ(Line.Fibers.fiber L a, U))
    (sb : Γ(Line.Fibers.fiber L b, U)) (sx : Γ(Line.Fibers.fiber L x, U)),
    (Dv.product b' y w hby).app U ((Dh.product c b b' hcb).app U sc sb)
      ((Dh.product a x y hax).app U sa sx) =
      (Dh.product a' z w haz).app U ((Dv.product c a a' hca).app U sc sa)
        ((Dv.product b x z hbx).app U sb sx)

/-- Equal coordinate maps retain the actual interchange law. -/
theorem congrCoordinates (Dh : FiberwiseMultiplication.Multiplication p r L) (Dv : FiberwiseMultiplication.Multiplication r p L)
    {p' : E ⟶ A} {r' : E ⟶ X} (hp : p = p') (hr : r = r') (hi : Interchange Dh Dv) :
    Interchange (MultiplicationCoordinates.congrCoordinates Dh hp hr)
      (MultiplicationCoordinates.congrCoordinates Dv hr hp) := by
  cases hp
  cases hr
  exact hi

/-- Pullback constructs the actual interchange law by transporting all nine line fibers coherently. -/
theorem pullback (q : K ⟶ E) (Dh : FiberwiseMultiplication.Multiplication p r L) (Dv : FiberwiseMultiplication.Multiplication r p L)
    (hi : Interchange Dh Dv) :
    Interchange (FiberwiseMultiplicationPullback.pullbackMultiplication p r q L Dh) (FiberwiseMultiplicationPullback.pullbackMultiplication r p q L Dv) := by
  intro T c a b x a' b' y z w hax hbx hcb hca hby haz U sc sa sb sx
  exact Bilinear.InterchangeTransport.interchange
    (Dh.product _ _ _ (FiberwiseMultiplicationPullback.imageRel p r q a x y hax)) (Dv.product _ _ _ (FiberwiseMultiplicationPullback.imageRel r p q b x z hbx))
    (Dh.product _ _ _ (FiberwiseMultiplicationPullback.imageRel p r q c b b' hcb)) (Dv.product _ _ _ (FiberwiseMultiplicationPullback.imageRel r p q c a a' hca))
    (Dv.product _ _ _ (FiberwiseMultiplicationPullback.imageRel r p q b' y w hby)) (Dh.product _ _ _ (FiberwiseMultiplicationPullback.imageRel p r q a' z w haz))
    (Pulled.LineBilinear.fiberComparison q L c (c ≫ q) rfl).symm (Pulled.LineBilinear.fiberComparison q L a (a ≫ q) rfl).symm
    (Pulled.LineBilinear.fiberComparison q L b (b ≫ q) rfl).symm (Pulled.LineBilinear.fiberComparison q L x (x ≫ q) rfl).symm
    (Pulled.LineBilinear.fiberComparison q L a' (a' ≫ q) rfl).symm (Pulled.LineBilinear.fiberComparison q L b' (b' ≫ q) rfl).symm
    (Pulled.LineBilinear.fiberComparison q L y (y ≫ q) rfl).symm (Pulled.LineBilinear.fiberComparison q L z (z ≫ q) rfl).symm
    (Pulled.LineBilinear.fiberComparison q L w (w ≫ q) rfl).symm
    (hi T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) U sc sa sb sx

variable {Z : Over S} [GrpObj Z] (φ : A ⟶ Z) [IsMonHom φ]

/-- Restricting the first group coordinate and the second fixed coordinate preserves interchange. -/
theorem restrictCoordinate (Dh : FiberwiseMultiplication.Multiplication (p ≫ φ) r L) (Dv : FiberwiseMultiplication.Multiplication r (p ≫ φ) L)
    (hi : Interchange Dh Dv) :
    Interchange (MultiplicationCoordinateMap.restrictCoordinate p r φ L Dh)
      (MultiplicationFixedMap.restrictFixed r p φ L Dv) := by
  intro T c a b x a' b' y z w hax hbx hcb hca hby haz U sc sa sb sx
  exact hi T c a b x a' b' y z w
    (MultiplicationCoordinateMap.mappedRel p r φ a x y hax)
    (MultiplicationFixedMap.mappedRel r p φ b x z hbx)
    (MultiplicationCoordinateMap.mappedRel p r φ c b b' hcb)
    (MultiplicationFixedMap.mappedRel r p φ c a a' hca)
    (MultiplicationFixedMap.mappedRel r p φ b' y w hby)
    (MultiplicationCoordinateMap.mappedRel p r φ a' z w haz) U sc sa sb sx

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseInterchange
