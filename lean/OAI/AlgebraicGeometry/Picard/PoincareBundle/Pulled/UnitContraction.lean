import OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineSection
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

/-! # Unit Contraction -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.UnitContraction

noncomputable section

/-! Contracting by a pulled target unit gives the actual canonical quotient-fiber comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineSection

variable {S : Scheme.{u}} {K E A X : Over S} [GrpObj A]
  (p : E ⟶ A) (r : E ⟶ X) (q : K ⟶ E)
  (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication p r L)

/-- The original left-unit law identifies the entire pulled contraction map. -/
theorem contraction_eq {T : Over S} (c a b : T ⟶ K) (c' x : T ⟶ E)
    (hc : c ≫ q = c') (ha : a ≫ q = x) (hb : b ≫ q = x)
    (hz : c' ≫ p = 1) (h : FiberwiseMultiplication.ProductRel p r c' x x) :
    Bilinear.Contraction.contractLeft
      (LineBilinear.transport q L c a b c' x x hc ha hb (D.product c' x x h))
      (LineSection.transportFrame q L c c' hc (D.unitFrame c' hz)).hom =
      (LineBilinear.fiberComparison q L a x ha).hom ≫ (LineBilinear.fiberComparison q L b x hb).inv := by
  unfold LineBilinear.transport LineSection.transportFrame
  rw [Iso.trans_hom, Bilinear.Transport.contractLeft_transport,
    Bilinear.ActionLaws.contraction_unit (D.product c' x x h) (D.unitFrame c' hz).hom
      (D.unit_left c' x hz h), Category.id_comp]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.UnitContraction
