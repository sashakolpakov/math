import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleCoefficientIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientTotal

/-! # Single Coefficient Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.SingleCoefficientCoordinates

noncomputable section

/-! Exact coefficient change in the literal ordered Cech complex
preserves the original single-degree total coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uA vA uB vB uD vD
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B] [HasCoproducts.{0} B]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (J : D ⥤ Cᵒᵖ ⥤ A) [J.Additive]
  (G : A ⥤ B) [G.Additive] [G.PreservesHomology] [PreservesLimitsOfSize.{u,u} G]

local instance finiteBiproducts : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts

abbrev sourceFunctor := J ⋙ OrderedCech.Functor.Projection.functor U
abbrev targetFunctor := J ⋙ (Functor.whiskeringRight Cᵒᵖ A B).obj G ⋙
  OrderedCech.Functor.Projection.functor U

def functorIso : IntegralComparison.Functor.SingleCoefficientChange.mappedFunctor (sourceFunctor U J) G ≅
    targetFunctor U J G :=
  NatIso.ofComponents (fun M => CoefficientChange.complexIso U G (J.obj M))
    (fun a => CoefficientChange.naturality U G _ (J.map a))

abbrev coefficientIso (M : D) (n : ℕ) :=
  IntegralComparison.Functor.SingleCoefficientIso.coefficientIso (sourceFunctor U J) G
    (targetFunctor U J G) (functorIso U J G) M n

theorem comparison (M : D) (c n : ℕ) :
    (CoefficientTotal.homologyIso U G
      ((J.mapHomologicalComplex (.up ℕ)).obj ((single D (.up ℕ) c).obj M)) (n+c)).hom ≫
      (IntegralComparison.Functor.SingleTotal.homologyIso (targetFunctor U J G) M c n).hom =
    G.map (IntegralComparison.Functor.SingleTotal.homologyIso (sourceFunctor U J) M c n).hom ≫
      (coefficientIso U J G M n).hom :=
  IntegralComparison.Functor.SingleCoefficientIso.comparison (sourceFunctor U J) G
    (targetFunctor U J G) (functorIso U J G) M c n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.SingleCoefficientCoordinates
