import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechTopClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTopEdgeDegree
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Cech Single Top Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechSingleTopCoordinates

noncomputable section

/-! The actual augmented top total class has the original signed
single-degree coordinate, with its total-degree transport explicit. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechTopClass
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → C)
  {R : Type v} [CommRing R] [HasProducts.{u} (ModuleCat.{w} R)]

theorem topTotalClass_transport (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ)
    (m : ℕ) (hm : Fintype.card ι = m) (c : ℕ)
    (outgoing : ∀ q, ((CechFunctor.bicomplex U K).d c (c+1)).f q = 0)
    (d : ℕ) (hd : c+m=d) (z : (K.X c).obj (op (CechCoordinates.topObject U m hm)))
    (hz : (K.d c (c+1)).app (op (CechCoordinates.topObject U m hm)) z = 0) :
    (eqToHom (congrArg (fun j => ((CechFunctor.bicomplex U K).total (.up ℕ)).homology j) hd))
        (CechLargeTop.topTotalClass U K m hm c z hz) =
      Single.ColumnTopEdgeDegree.Row.mapTo (CechFunctor.bicomplex U K) c outgoing m d hd
        (CechTopClass.topClass U (K.X c) m hm z) := by
  cases hd
  exact CechTopClass.topTotalClass_edge U m hm K c outgoing z hz

abbrev coefficientSingle (N : Cᵒᵖ ⥤ ModuleCat.{w} R) (c : ℕ) :=
  (single (Cᵒᵖ ⥤ ModuleCat.{w} R) (.up ℕ) c).obj N

variable (N : Cᵒᵖ ⥤ ModuleCat.{w} R) (m : ℕ) (hm : Fintype.card ι = m) (c : ℕ)

abbrev singleValue (z : N.obj (op (CechCoordinates.topObject U m hm))) :=
  (singleObjXSelf (.up ℕ) c N).inv.app (op (CechCoordinates.topObject U m hm)) z

omit [HasProducts (ModuleCat R)] in
theorem singleValue_closed (z : N.obj (op (CechCoordinates.topObject U m hm))) :
    ((coefficientSingle N c).d c (c+1)).app (op (CechCoordinates.topObject U m hm))
      (singleValue U N m hm c z) = 0 := by
  rw [single_obj_d]
  rfl

theorem topTotalClass_coordinates (z : N.obj (op (CechCoordinates.topObject U m hm)))
    (hz : ((coefficientSingle N c).d c (c+1)).app (op (CechCoordinates.topObject U m hm))
      (singleValue U N m hm c z) = 0) :
    (Functor.SingleTotal.homologyIso (CechFunctor.functor U) N c m).hom
      ((eqToHom (congrArg
        (fun j => ((CechFunctor.bicomplex U (coefficientSingle N c)).total (.up ℕ)).homology j)
        (Nat.add_comm c m)))
        (CechLargeTop.topTotalClass U (coefficientSingle N c)
          m hm c (singleValue U N m hm c z) hz)) =
      ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) c m • CechTopClass.topClass U N m hm z := by
  let outgoing := Functor.SingleTopEdge.outgoing (CechFunctor.functor U) N c
  have hrow : homologyMap (Functor.SingleTotal.rowIso (CechFunctor.functor U) N c).hom m
      (CechTopClass.topClass U ((coefficientSingle N c).X c) m hm (singleValue U N m hm c z)) =
      CechTopClass.topClass U N m hm z := by
    change homologyMap (CechFunctor.complexMap U (singleObjXSelf (.up ℕ) c N).hom) m
      (CechTopClass.topClass U ((coefficientSingle N c).X c) m hm (singleValue U N m hm c z)) = _
    rw [CechTopClass.topClass_naturality]
    apply congrArg (CechTopClass.topClass U N m hm)
    exact ConcreteCategory.congr_hom
      (congrArg (fun a : N ⟶ N => a.app (op (CechCoordinates.topObject U m hm)))
        (singleObjXSelf (.up ℕ) c N).inv_hom_id) z
  erw [topTotalClass_transport U (coefficientSingle N c) m hm c outgoing
    (m+c) (Nat.add_comm c m) (singleValue U N m hm c z) hz]
  change homologyMap (Functor.SingleTotal.rowIso (CechFunctor.functor U) N c).hom m
    ((Single.ColumnCycleCoordinates.homologyIso
      (Functor.SingleTotal.bicomplex (CechFunctor.functor U) N c) c
      (Functor.SingleTotal.off_degree (CechFunctor.functor U) N c) m).hom _) = _
  erw [Single.ColumnTopEdgeDegree.map_apply
    (Functor.SingleTotal.bicomplex (CechFunctor.functor U) N c) c
    (Functor.SingleTotal.off_degree (CechFunctor.functor U) N c) outgoing m]
  simpa only [Units.smul_def, map_zsmul] using congrArg
    (fun x => ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) c m • x) hrow

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechSingleTopCoordinates
