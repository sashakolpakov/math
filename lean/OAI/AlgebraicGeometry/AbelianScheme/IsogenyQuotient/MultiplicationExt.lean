import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits

/-! # Multiplication Ext -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationExt.Construction

noncomputable section

/-! The genuine products determine their normalized unit frames,
and therefore determine the entire PoincareBundle multiplication structure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u

variable {S : Scheme.{u}} {E A X : Over S} [GrpObj A]
  {p : E ⟶ A} {r : E ⟶ X} {L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left}
  (D F : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication p r L)

theorem multiplication_unitFrame_eq_of_products
    (h : ∀ {T : Over S} (a b c : T ⟶ E) (hc : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel p r a b c), D.product a b c hc = F.product a b c hc)
    {T : Over S} (a : T ⟶ E) (ha : a ≫ p = 1) : D.unitFrame a ha = F.unitFrame a ha := by
  apply Iso.ext
  apply Picard.PoincareBundle.Line.FrameUnits.unit_hom_ext
  intro U
  have hp : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel p r a a a := ⟨by rw [ha, one_mul], rfl, rfl⟩
  have hl := D.unit_left a a ha hp U ((F.unitFrame a ha).hom.app U (1 : Γ(T.left, U)))
  have hr := F.unit_right a a ha hp U ((D.unitFrame a ha).hom.app U (1 : Γ(T.left, U)))
  rw [h a a a hp] at hl
  exact hr.symm.trans hl

theorem multiplication_eq_of_products
    (h : ∀ {T : Over S} (a b c : T ⟶ E) (hc : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel p r a b c), D.product a b c hc = F.product a b c hc) :
    D = F := by
  have hprod : @D.product = @F.product := by
    funext T a b c hc
    exact h a b c hc
  have hframe : @D.unitFrame = @F.unitFrame := by
    funext T a ha
    exact multiplication_unitFrame_eq_of_products D F h a ha
  cases D
  cases F
  cases hprod
  cases hframe
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationExt.Construction
