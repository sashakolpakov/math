import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Augmentation

/-! # Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement

noncomputable section

/-! Refinement acts on the original nonempty-tuple Cech complex,
using only binary products of objects in the underlying category. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial _root_.AlgebraicTopology

universe u v w z t
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Preadditive A] [HasProducts.{t} A]
  {ι κ : Type t} (U : ι → C) (V : κ → C)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

def nerveMap : IntegralComparison.NonemptyCechNerve.nerve V ⟶ IntegralComparison.NonemptyCechNerve.nerve U where
  app n := FormalCoproduct.powerMap r (Fin (n.unop.len + 1))
  naturality _ _ f := FormalCoproduct.mapPower_powerMap r f.unop.toOrderHom.toFun

def cosimplicialMap (P : Cᵒᵖ ⥤ A) :
    (FormalCoproduct.cosimplicialObjectFunctor (IntegralComparison.NonemptyCechNerve.nerve U)).obj P ⟶
      (FormalCoproduct.cosimplicialObjectFunctor (IntegralComparison.NonemptyCechNerve.nerve V)).obj P :=
  Functor.whiskerRight (nerveMap U V r).rightOp ((FormalCoproduct.evalOp C A).obj P)

def map (P : Cᵒᵖ ⥤ A) : (IntegralComparison.NonemptyCechNerve.complexFunctor U).obj P ⟶
    (IntegralComparison.NonemptyCechNerve.complexFunctor V).obj P :=
  (alternatingCofaceMapComplex A).map (cosimplicialMap U V r P)

theorem naturality {P Q : Cᵒᵖ ⥤ A} (a : P ⟶ Q) :
    (IntegralComparison.NonemptyCechNerve.complexFunctor U).map a ≫ NonemptyCechRefinement.map U V r Q =
      NonemptyCechRefinement.map U V r P ≫ (IntegralComparison.NonemptyCechNerve.complexFunctor V).map a := by
  ext n : 1
  exact (((FormalCoproduct.evalOp C A).map a).naturality
    ((nerveMap U V r).app (op (SimplexCategory.mk n))).op).symm

def transformation : IntegralComparison.NonemptyCechNerve.complexFunctor (A := A) U ⟶
    IntegralComparison.NonemptyCechNerve.complexFunctor (A := A) V where
  app P := NonemptyCechRefinement.map U V r P
  naturality _ _ a := NonemptyCechRefinement.naturality U V r a

omit [Preadditive A] in
theorem restriction (P : Cᵒᵖ ⥤ A) (M : A) (η : (Functor.const Cᵒᵖ).obj M ⟶ P)
    (n : SimplexCategory) :
    (Augmentation.NonemptyCechAugmentation.restriction U P M η).app n ≫ (cosimplicialMap U V r P).app n =
      (Augmentation.NonemptyCechAugmentation.restriction V P M η).app n := by
  let En := (IntegralComparison.NonemptyCechNerve.nerve U).obj (op n)
  let Em := (IntegralComparison.NonemptyCechNerve.nerve V).obj (op n)
  let a := (nerveMap U V r).app (op n)
  change Pi.lift (fun i : En.I => η.app (op (En.obj i))) ≫
      Pi.lift (fun i : Em.I => Pi.π (fun j : En.I => P.obj (op (En.obj j))) (a.f i) ≫
        P.map (a.φ i).op) = Pi.lift (fun i : Em.I => η.app (op (Em.obj i)))
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
  exact (η.naturality (a.φ i).op).symm.trans
    ((Category.id_comp _).trans (Pi.lift_comp_π (fun i : Em.I => η.app (op (Em.obj i))) i).symm)

variable [HasZeroObject A]

theorem augmentation (P : Cᵒᵖ ⥤ A) (M : A) (η : (Functor.const Cᵒᵖ).obj M ⟶ P) :
    Augmentation.NonemptyCechAugmentation.augmentation U P M η ≫ NonemptyCechRefinement.map U V r P =
      Augmentation.NonemptyCechAugmentation.augmentation V P M η := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, Augmentation.NonemptyCechAugmentation.augmentation_zero,
    Augmentation.NonemptyCechAugmentation.augmentation_zero]
  exact restriction U V r P M η ⦋0⦌

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement
