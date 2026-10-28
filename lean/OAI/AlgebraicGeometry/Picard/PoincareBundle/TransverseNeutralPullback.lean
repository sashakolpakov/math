import OAI.AlgebraicGeometry.Picard.PoincareBundle.InterchangeNeutralFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationCoordinates

/-! # Transverse Neutral Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseNeutralPullback

noncomputable section

/-!
# Transverse neutral-frame multiplication survives actual geometric pullback
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationPullback
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear

variable {S : Scheme.{u}} {E A X K : Over S} [GrpObj A] [GrpObj X]
  {p : E ⟶ A} {r : E ⟶ X} {L : Line.Bundles.LineBundle E.left}

/-- The first normalized neutral frames respect the genuine multiplication in the other coordinate. -/
def TransverseUnits (Dh : FiberwiseMultiplication.Multiplication p r L) (Dv : FiberwiseMultiplication.Multiplication r p L) : Prop :=
  ∀ (T : Over S) (a b c : T ⟶ E) (ha : a ≫ p = 1) (hb : b ≫ p = 1) (hc : c ≫ p = 1)
    (h : FiberwiseMultiplication.ProductRel r p a b c) (U : T.left.Opens),
    (Dv.product a b c h).app U ((Dh.unitFrame a ha).hom.app U (1 : Γ(T.left, U)))
      ((Dh.unitFrame b hb).hom.app U (1 : Γ(T.left, U))) = (Dh.unitFrame c hc).hom.app U (1 : Γ(T.left, U))

/-- Equal actual coordinates preserve the transverse neutral-frame law. -/
theorem congrCoordinates (Dh : FiberwiseMultiplication.Multiplication p r L) (Dv : FiberwiseMultiplication.Multiplication r p L)
    {p' : E ⟶ A} {r' : E ⟶ X} (hp : p = p') (hr : r = r') (h : TransverseUnits Dh Dv) :
    TransverseUnits (MultiplicationCoordinates.congrCoordinates Dh hp hr)
      (MultiplicationCoordinates.congrCoordinates Dv hr hp) := by
  cases hp
  cases hr
  exact h

/-- The full transverse law pulls back through the canonical geometric fiber comparisons. -/
theorem pullback (q : K ⟶ E) (Dh : FiberwiseMultiplication.Multiplication p r L) (Dv : FiberwiseMultiplication.Multiplication r p L)
    (ht : TransverseUnits Dh Dv) :
    TransverseUnits (FiberwiseMultiplicationPullback.pullbackMultiplication p r q L Dh) (FiberwiseMultiplicationPullback.pullbackMultiplication r p q L Dv) := by
  intro T a b c ha hb hc h U
  exact Bilinear.FrameProducts.product_transport
    (Dv.product _ _ _ (FiberwiseMultiplicationPullback.imageRel r p q a b c h))
    (Pulled.LineBilinear.fiberComparison q L a (a ≫ q) rfl).symm (Pulled.LineBilinear.fiberComparison q L b (b ≫ q) rfl).symm
    (Pulled.LineBilinear.fiberComparison q L c (c ≫ q) rfl).symm
    (Dh.unitFrame _ (FiberwiseMultiplicationPullback.imageUnit p q a ha)).hom (Dh.unitFrame _ (FiberwiseMultiplicationPullback.imageUnit p q b hb)).hom
    (Dh.unitFrame _ (FiberwiseMultiplicationPullback.imageUnit p q c hc)).hom
    (ht T _ _ _ (FiberwiseMultiplicationPullback.imageUnit p q a ha) (FiberwiseMultiplicationPullback.imageUnit p q b hb) (FiberwiseMultiplicationPullback.imageUnit p q c hc)
      (FiberwiseMultiplicationPullback.imageRel r p q a b c h)) U

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseNeutralPullback
