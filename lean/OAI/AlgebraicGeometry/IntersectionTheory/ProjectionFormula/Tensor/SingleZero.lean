import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Cochain
import Mathlib.Algebra.Homology.Single

/-! # Single Zero -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SingleZero

noncomputable section

/-! Tensoring with a module in degree zero is the degreewise tensor functor. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open scoped Classical

variable (R : Type) [CommRing R]

abbrev singleZero (M : ModuleCat.{0} R) : CochainComplex (ModuleCat.{0} R) ℤ :=
  (HomologicalComplex.single (ModuleCat.{0} R) (.up ℤ) 0).obj M

local instance hasMapBifunctor (P Q : CochainComplex (ModuleCat.{0} R) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor (ModuleCat.{0} R)) (.up ℤ) := by
  intro n
  infer_instance

variable (M : ModuleCat.{0} R) (K : CochainComplex (ModuleCat.{0} R) ℤ)

def termHom (n : ℤ) : ((Homotopy.complexFunctor R K).obj (singleZero R M)).X n ⟶
    (tensorLeft M).obj (K.X n) :=
  HomologicalComplex.mapBifunctorDesc (fun i j hij =>
    if hi : i = 0 then
      ((curriedTensor (ModuleCat.{0} R)).map
        (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M i hi).hom).app (K.X j) ≫
        (tensorLeft M).map (K.XIsoOfEq (by change i + j = n at hij; omega)).hom
    else 0)

def termInv (n : ℤ) : (tensorLeft M).obj (K.X n) ⟶
    ((Homotopy.complexFunctor R K).obj (singleZero R M)).X n :=
  ((curriedTensor (ModuleCat.{0} R)).map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv).app (K.X n) ≫
    HomologicalComplex.ιMapBifunctor (singleZero R M) K (curriedTensor (ModuleCat.{0} R)) (.up ℤ)
      0 n n (zero_add n)

@[reassoc]
theorem ι_termHom (n : ℤ) :
    HomologicalComplex.ιMapBifunctor (singleZero R M) K (curriedTensor (ModuleCat.{0} R)) (.up ℤ)
      0 n n (zero_add n) ≫ termHom R M K n =
      ((curriedTensor (ModuleCat.{0} R)).map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom).app (K.X n) := by
  simp only [termHom, HomologicalComplex.ι_mapBifunctorDesc, dite_true,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  rw [(tensorLeft M).map_id, Category.comp_id]
  rfl

theorem termInv_termHom (n : ℤ) : termInv R M K n ≫ termHom R M K n = 𝟙 _ := by
  rw [termInv, Category.assoc, ι_termHom, ← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, NatTrans.id_app]

theorem termHom_termInv (n : ℤ) : termHom R M K n ≫ termInv R M K n = 𝟙 _ := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  change i + j = n at hij
  by_cases hi : i = 0
  · subst i
    obtain rfl : j = n := by omega
    rw [ι_termHom_assoc, termInv, ← NatTrans.comp_app_assoc, ← CategoryTheory.Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
    exact (Category.comp_id _).symm
  · have hz : IsZero (((curriedTensor (ModuleCat.{0} R)).obj ((singleZero R M).X i)).obj (K.X j)) :=
      (tensorRight (K.X j)).map_isZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)
    exact hz.eq_of_src _ _

def termIso (n : ℤ) : ((Homotopy.complexFunctor R K).obj (singleZero R M)).X n ≅
    (tensorLeft M).obj (K.X n) where
  hom := termHom R M K n
  inv := termInv R M K n
  hom_inv_id := termHom_termInv R M K n
  inv_hom_id := termInv_termHom R M K n

theorem comm (n m : ℤ) (hnm : n + 1 = m) :
    termHom R M K n ≫ (tensorLeft M).map (K.d n m) =
      ((Homotopy.complexFunctor R K).obj (singleZero R M)).d n m ≫ termHom R M K m := by
  subst m
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  change i + j = n at hij
  by_cases hi : i = 0
  · subst i
    have hj : j = n := by omega
    subst j
    rw [ι_termHom_assoc,
      Cochain.ι_d_assoc R K n (n + 1) 0 n 1 (n + 1) rfl (zero_add n) rfl rfl]
    simp only [HomologicalComplex.single_obj_d, CategoryTheory.Functor.map_zero,
      NatTrans.app_zero, zero_comp, zero_add, Int.negOnePow_zero, one_smul, Category.assoc]
    rw [ι_termHom]
    exact (((curriedTensor (ModuleCat.{0} R)).map
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom).naturality (K.d n (n + 1))).symm
  · have hz : IsZero (((curriedTensor (ModuleCat.{0} R)).obj ((singleZero R M).X i)).obj (K.X j)) :=
      (tensorRight (K.X j)).map_isZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)
    exact hz.eq_of_src _ _

def iso : (Homotopy.complexFunctor R K).obj (singleZero R M) ≅
    ((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents (termIso R M K) (fun n m h => comm R M K n m h)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SingleZero
