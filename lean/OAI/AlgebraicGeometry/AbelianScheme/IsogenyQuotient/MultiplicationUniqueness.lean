import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationExt
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationOriginComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeParameterFactors
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeParameter

/-! # Multiplication Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationUniqueness.Construction

noncomputable section

/-! Multiplication of line fibers over a product of proper smooth
connected commutative groups is determined by its origin unit frame.
The comparison covers every test scheme through universal parameters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u

variable {k : Type u} [Field k] (G X : Over (Spec (.of k)))
  [GrpObj G] [GrpObj X] [IsCommMonObj G] [IsCommMonObj X]
  [Smooth G.hom] [Smooth X.hom] [IsProper G.hom] [IsProper X.hom]
  [GeometricallyConnected G.hom] [GeometricallyConnected X.hom]
  (L : Picard.PoincareBundle.Line.Bundles.LineBundle (G ⊗ X).left)

attribute [local instance] InterchangeParameter.Construction.lineInterchangeParameter_smooth InterchangeParameter.Construction.lineInterchangeParameter_proper
  InterchangeParameter.Construction.lineInterchangeParameter_connected

theorem horizontalMultiplication_eq_of_origin
    (D F : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst G X) (snd G X) L)
    (hs : D.unitFrame (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G ⊗ X) (MonObj.one_comp (fst G X)) =
      F.unitFrame 1 (MonObj.one_comp (fst G X))) : D = F := by
  apply MultiplicationExt.Construction.multiplication_eq_of_products D F
  intro T a b c h
  let U := InterchangeParameters.Construction.lineInterchangeParameter G X
  let a0 := InterchangeParameters.Construction.lineInterchangePointC G X
  let b0 := InterchangeParameters.Construction.lineInterchangePointB G X
  let c0 := InterchangeParameters.Construction.lineInterchangePointCB G X
  let h0 := InterchangeParameters.Construction.lineInterchangeRelationCB G X
  have hp := MultiplicationOriginComparison.Construction.multiplication_group_products_eq_of_origin D F hs U a0 b0 c0 h0
  let q := InterchangeParameterFactors.Construction.lineInterchangeParameterLift a a b
  have ha : q ≫ a0 = a := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointC a a b
  have hb : q ≫ b0 = b := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointB a a b h.2.1
  have hc : q ≫ c0 = c := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointCB a a b c h
  have he := congrArg (Picard.PoincareBundle.Line.Fibers.pullBilinear L q a0 b0 c0 a b c ha hb hc) hp
  exact (D.product_natural q a0 b0 c0 h0 a b c h ha hb hc).symm.trans
    (he.trans (F.product_natural q a0 b0 c0 h0 a b c h ha hb hc))

theorem verticalMultiplication_eq_of_origin
    (D F : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd G X) (fst G X) L)
    (hs : D.unitFrame (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G ⊗ X) (MonObj.one_comp (snd G X)) =
      F.unitFrame 1 (MonObj.one_comp (snd G X))) : D = F := by
  apply MultiplicationExt.Construction.multiplication_eq_of_products D F
  intro T a b c h
  let U := InterchangeParameters.Construction.lineInterchangeParameter G X
  let a0 := InterchangeParameters.Construction.lineInterchangePointC G X
  let b0 := InterchangeParameters.Construction.lineInterchangePointA G X
  let c0 := InterchangeParameters.Construction.lineInterchangePointCA G X
  let h0 := InterchangeParameters.Construction.lineInterchangeRelationCA G X
  have hp := MultiplicationOriginComparison.Construction.multiplication_group_products_eq_of_origin D F hs U a0 b0 c0 h0
  let q := InterchangeParameterFactors.Construction.lineInterchangeParameterLift a b a
  have ha : q ≫ a0 = a := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointC a b a
  have hb : q ≫ b0 = b := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointA a b a h.2.1
  have hc : q ≫ c0 = c := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointCA a b a c h
  have he := congrArg (Picard.PoincareBundle.Line.Fibers.pullBilinear L q a0 b0 c0 a b c ha hb hc) hp
  exact (D.product_natural q a0 b0 c0 h0 a b c h ha hb hc).symm.trans
    (he.trans (F.product_natural q a0 b0 c0 h0 a b c h ha hb hc))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationUniqueness.Construction
