import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.TopClassCoefficients
import Mathlib.Algebra.Category.Grp.Ulift

/-! # Top Class Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.TopClassLift

noncomputable section

/-! The original full-intersection class under scalar forgetting and
under the two additive universe lifts used by native coefficients. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w

section Forget
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → C)
  {R : Type v} [CommRing R] [HasProducts.{u} (ModuleCat.{w} R)]
  [HasProducts.{u} AddCommGrpCat.{w}]
  [PreservesLimitsOfSize.{u,u} (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})]
  (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (m : ℕ) (hm : Fintype.card ι = m)

theorem forget (x : P.obj (op (AugmentedOrdered.CechCoordinates.topObject U m hm))) :
    (AugmentedCech.TopClassCoefficients.homologyIso U
      (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) P m).hom
        (AugmentedOrdered.CechTopClass.topClass U P m hm x) =
    AugmentedCech.TopClassMap.map U
      (P ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) m hm x := by
  rw [← AugmentedCech.TopClassMap.module_apply]
  exact ConcreteCategory.congr_hom
    (AugmentedCech.TopClassCoefficients.comparison U
      (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) P m hm) x
end Forget

abbrev liftFunctor : AddCommGrpCat.{0} ⥤ AddCommGrpCat.{2} :=
  AddCommGrpCat.uliftFunctor.{1,0} ⋙ AddCommGrpCat.uliftFunctor.{2,1}

variable {C : Type} [Preorder C] [HasFiniteProducts C]
  {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ AddCommGrpCat.{0}) (m : ℕ) (hm : Fintype.card ι = m)

theorem lift (x : P.obj (op (AugmentedOrdered.CechCoordinates.topObject U m hm))) :
    (AugmentedCech.TopClassCoefficients.homologyIso U liftFunctor P m).hom
      (ULift.up.{2,1} (ULift.up.{1,0} (AugmentedCech.TopClassMap.map U P m hm x))) =
    AugmentedCech.TopClassMap.map U (P ⋙ liftFunctor) m hm
      (ULift.up.{2,1} (ULift.up.{1,0} x)) := by
  exact ConcreteCategory.congr_hom
    (AugmentedCech.TopClassCoefficients.comparison U liftFunctor P m hm)
    (ULift.up.{2,1} (ULift.up.{1,0} x))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.TopClassLift
