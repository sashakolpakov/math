import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeParameterFactors
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeParameter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.GroupInterchange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberInterchangePullback

/-! # Interchange -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.Interchange.Construction

noncomputable section

/-! The actual original horizontal and vertical Poincare products
satisfy interchange on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

attribute [local instance] InterchangeParameter.Construction.lineInterchangeParameter_smooth InterchangeParameter.Construction.lineInterchangeParameter_proper InterchangeParameter.Construction.lineInterchangeParameter_connected

theorem poincareProducts_interchange {T : Over (Spec (.of k))}
    (c a b x ca cb ax bx w : T ⟶ D.abelian.scheme ⊗ A.scheme)
    (hax : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) a x ax)
    (hbx : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) b x bx)
    (hcb : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) c b cb)
    (hca : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) c a ca)
    (hby : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) cb ax w)
    (haz : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) ca bx w)
    (U : T.left.Opens) (sc : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) c, U))
    (sa : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) a, U)) (sb : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) b, U))
    (sx : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x, U)) :
    (VerticalProduct.Construction.poincareVerticalProduct D cb ax w hby).app U ((HorizontalProduct.Construction.poincareHorizontalProduct D c b cb hcb).app U sc sb)
      ((HorizontalProduct.Construction.poincareHorizontalProduct D a x ax hax).app U sa sx) =
    (HorizontalProduct.Construction.poincareHorizontalProduct D ca bx w haz).app U ((VerticalProduct.Construction.poincareVerticalProduct D c a ca hca).app U sc sa)
      ((VerticalProduct.Construction.poincareVerticalProduct D b x bx hbx).app U sb sx) := by
  let c₀ := InterchangeParameters.Construction.lineInterchangePointC D.abelian.scheme A.scheme
  let a₀ := InterchangeParameters.Construction.lineInterchangePointA D.abelian.scheme A.scheme
  let b₀ := InterchangeParameters.Construction.lineInterchangePointB D.abelian.scheme A.scheme
  let x₀ := InterchangeParameters.Construction.lineInterchangePointX D.abelian.scheme A.scheme
  let ca₀ := InterchangeParameters.Construction.lineInterchangePointCA D.abelian.scheme A.scheme
  let cb₀ := InterchangeParameters.Construction.lineInterchangePointCB D.abelian.scheme A.scheme
  let ax₀ := InterchangeParameters.Construction.lineInterchangePointAX D.abelian.scheme A.scheme
  let bx₀ := InterchangeParameters.Construction.lineInterchangePointBX D.abelian.scheme A.scheme
  let w₀ := InterchangeParameters.Construction.lineInterchangePointW D.abelian.scheme A.scheme
  let r := InterchangeParameterFactors.Construction.lineInterchangeParameterLift c a b
  have hc : r ≫ c₀ = c := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointC c a b
  have ha : r ≫ a₀ = a := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointA c a b hca.2.1
  have hb : r ≫ b₀ = b := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointB c a b hcb.2.1
  have hx : r ≫ x₀ = x := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointX c a b x hbx.2.1 hax.2.1
  have hca' : r ≫ ca₀ = ca := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointCA c a b ca hca
  have hcb' : r ≫ cb₀ = cb := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointCB c a b cb hcb
  have hax' : r ≫ ax₀ = ax := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointAX c a b x ax hca.2.1 hbx.2.1 hax
  have hbx' : r ≫ bx₀ = bx := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointBX c a b x bx hcb.2.1 hax.2.1 hbx
  have hw : r ≫ w₀ = w := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointW c a b cb ax w hcb hax.2.2 hby
  have hax₀ := InterchangeParameters.Construction.lineInterchangeRelationAX D.abelian.scheme A.scheme
  have hbx₀ := InterchangeParameters.Construction.lineInterchangeRelationBX D.abelian.scheme A.scheme
  have hcb₀ := InterchangeParameters.Construction.lineInterchangeRelationCB D.abelian.scheme A.scheme
  have hca₀ := InterchangeParameters.Construction.lineInterchangeRelationCA D.abelian.scheme A.scheme
  have hby₀ := InterchangeParameters.Construction.lineInterchangeRelationBY D.abelian.scheme A.scheme
  have haz₀ := InterchangeParameters.Construction.lineInterchangeRelationAZ D.abelian.scheme A.scheme
  have hg := GroupInterchange.Construction.poincareGroupProducts_interchange D c₀ a₀ b₀ x₀ ca₀ cb₀ ax₀ bx₀ w₀ hax₀ hbx₀ hcb₀ hca₀ hby₀ haz₀
  have hp := FiberInterchangePullback.Construction.fiberBilinear_interchange_pullback (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) r
    c₀ a₀ b₀ x₀ ca₀ cb₀ ax₀ bx₀ w₀ c a b x ca cb ax bx w hc ha hb hx hca' hcb' hax' hbx' hw
    (HorizontalProduct.Construction.poincareHorizontalProduct D a₀ x₀ ax₀ hax₀) (VerticalProduct.Construction.poincareVerticalProduct D b₀ x₀ bx₀ hbx₀)
    (HorizontalProduct.Construction.poincareHorizontalProduct D c₀ b₀ cb₀ hcb₀) (VerticalProduct.Construction.poincareVerticalProduct D c₀ a₀ ca₀ hca₀)
    (VerticalProduct.Construction.poincareVerticalProduct D cb₀ ax₀ w₀ hby₀) (HorizontalProduct.Construction.poincareHorizontalProduct D ca₀ bx₀ w₀ haz₀) hg U sc sa sb sx
  rw [VerticalProduct.Construction.poincareVerticalProduct_natural D r cb₀ ax₀ w₀ hby₀ cb ax w hby hcb' hax' hw,
    HorizontalProduct.Construction.poincareHorizontalProduct_natural D r c₀ b₀ cb₀ hcb₀ c b cb hcb hc hb hcb',
    HorizontalProduct.Construction.poincareHorizontalProduct_natural D r a₀ x₀ ax₀ hax₀ a x ax hax ha hx hax',
    HorizontalProduct.Construction.poincareHorizontalProduct_natural D r ca₀ bx₀ w₀ haz₀ ca bx w haz hca' hbx' hw,
    VerticalProduct.Construction.poincareVerticalProduct_natural D r c₀ a₀ ca₀ hca₀ c a ca hca hc ha hca',
    VerticalProduct.Construction.poincareVerticalProduct_natural D r b₀ x₀ bx₀ hbx₀ b x bx hbx hb hx hbx'] at hp
  exact hp

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.Interchange.Construction
