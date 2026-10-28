import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.FrameProducts

/-! # Fiber Products -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.FiberProducts

noncomputable section

/-!
# The actual normalized unit fibers multiply correctly, including after arbitrary line pullback
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear

variable {S : Scheme.{u}} {E A X : Over S} [GrpObj A] (p : E ⟶ A) (r : E ⟶ X)
  [Mono (lift p r)] (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication p r L)

/-- On a genuine product-coordinate space, the normalized frames at three neutral fibers obey multiplication. -/
theorem unitFrame_product {T : Over S} (a b c : T ⟶ E)
    (ha : a ≫ p = 1) (hb : b ≫ p = 1) (hc : c ≫ p = 1) (h : FiberwiseMultiplication.ProductRel p r a b c) (U : T.left.Opens) :
    (D.product a b c h).app U ((D.unitFrame a ha).hom.app U (1 : Γ(T.left, U)))
      ((D.unitFrame b hb).hom.app U (1 : Γ(T.left, U))) = (D.unitFrame c hc).hom.app U (1 : Γ(T.left, U)) := by
  have hac : a = c := by
    apply (cancel_mono (lift p r)).mp
    rw [comp_lift, comp_lift]
    exact congrArg₂ lift (ha.trans hc.symm) h.2.2
  have hbc : b = c := by
    apply (cancel_mono (lift p r)).mp
    rw [comp_lift, comp_lift]
    exact congrArg₂ lift (hb.trans hc.symm) (h.2.1.symm.trans h.2.2)
  subst a
  subst b
  exact D.unit_left c c hc h U ((D.unitFrame c hc).hom.app U (1 : Γ(T.left, U)))

variable {K : Over S} (q : K ⟶ E)

/-- Canonical pullback of normalized unit frames preserves their multiplication without any subgroup splitting assumption. -/
theorem pullback_unitFrame_product {T : Over S} (a b c : T ⟶ K)
    (ha : a ≫ (q ≫ p) = 1) (hb : b ≫ (q ≫ p) = 1) (hc : c ≫ (q ≫ p) = 1)
    (h : FiberwiseMultiplication.ProductRel (q ≫ p) (q ≫ r) a b c) (U : T.left.Opens) :
    ((FiberwiseMultiplicationPullback.pullbackMultiplication p r q L D).product a b c h).app U
      (((FiberwiseMultiplicationPullback.pullbackMultiplication p r q L D).unitFrame a ha).hom.app U (1 : Γ(T.left, U)))
      (((FiberwiseMultiplicationPullback.pullbackMultiplication p r q L D).unitFrame b hb).hom.app U (1 : Γ(T.left, U))) =
      ((FiberwiseMultiplicationPullback.pullbackMultiplication p r q L D).unitFrame c hc).hom.app U (1 : Γ(T.left, U)) :=
  Bilinear.FrameProducts.product_transport
    (D.product _ _ _ (FiberwiseMultiplicationPullback.imageRel p r q a b c h))
    (Pulled.LineBilinear.fiberComparison q L a (a ≫ q) rfl).symm (Pulled.LineBilinear.fiberComparison q L b (b ≫ q) rfl).symm
    (Pulled.LineBilinear.fiberComparison q L c (c ≫ q) rfl).symm
    (D.unitFrame _ (FiberwiseMultiplicationPullback.imageUnit p q a ha)).hom
    (D.unitFrame _ (FiberwiseMultiplicationPullback.imageUnit p q b hb)).hom
    (D.unitFrame _ (FiberwiseMultiplicationPullback.imageUnit p q c hc)).hom
    (unitFrame_product p r L D _ _ _ _ _ _ _) U

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.FiberProducts
