import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SingleZero
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Tensor Single -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.TensorSingle

noncomputable section

section

/-! Tensoring with a module concentrated in any degree, and the homology
of this tensor when the module is flat. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable (R : Type) [CommRing R] (M : ModuleCat.{0} R)
  (K : CochainComplex (ModuleCat.{0} R) ℤ) (d : ℤ)

def iso :
    (Homotopy.complexFunctor R K).obj ((CochainComplex.singleFunctor (ModuleCat.{0} R) d).obj M) ≅
      (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj K)⟦-d⟧ :=
  (Homotopy.complexFunctor R K).mapIso
    (((CochainComplex.singleFunctors (ModuleCat.{0} R)).shiftIso (-d) d 0 (neg_add_cancel d)).symm.app M) ≪≫
      ((Homotopy.complexFunctor R K).commShiftIso (-d)).app _ ≪≫
      (CategoryTheory.shiftFunctor _ (-d)).mapIso (SingleZero.iso R M K)

def homologyIso (n : ℤ) :
    ((Homotopy.complexFunctor R K).obj
      ((CochainComplex.singleFunctor (ModuleCat.{0} R) d).obj M)).homology n ≅
    (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj K).homology (n - d) :=
  HomologicalComplex.homologyMapIso (iso R M K d) n ≪≫
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{0} R) (-d) n (n - d) (by omega)).app _

def flatHomologyIso [Module.Flat R M] (n : ℤ) :
    ((Homotopy.complexFunctor R K).obj
      ((CochainComplex.singleFunctor (ModuleCat.{0} R) d).obj M)).homology n ≅
    (tensorLeft M).obj (K.homology (n - d)) :=
  homologyIso R M K d n ≪≫ (K.sc (n - d)).mapHomologyIso (tensorLeft M)

end

/-! Naturality in the module of the tensor comparison for a single complex. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

namespace Naturality

variable (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℤ)
  {M N : ModuleCat.{0} R} (f : M ⟶ N)

local instance hasMapBifunctor (P Q : CochainComplex (ModuleCat.{0} R) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor (ModuleCat.{0} R)) (.up ℤ) := by
  intro n
  infer_instance

theorem naturality :
    (Homotopy.complexFunctor R K).map
      ((HomologicalComplex.single (ModuleCat.{0} R) (.up ℤ) 0).map f) ≫
        (SingleZero.iso R N K).hom =
      (SingleZero.iso R M K).hom ≫
        (NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{0} R)).map f) (.up ℤ)).app K := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (HomologicalComplex.mapBifunctorMap
    ((HomologicalComplex.single (ModuleCat.{0} R) (.up ℤ) 0).map f) (𝟙 K)
    (curriedTensor (ModuleCat.{0} R)) (.up ℤ)).f n ≫ SingleZero.termHom R N K n =
      SingleZero.termHom R M K n ≫ ((curriedTensor (ModuleCat.{0} R)).map f).app (K.X n)
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  change i + j = n at hij
  by_cases hi : i = 0
  · subst i
    have hj : j = n := by omega
    subst j
    rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
    simp only [HomologicalComplex.id_f]
    rw [((curriedTensor (ModuleCat.{0} R)).obj ((SingleZero.singleZero R N).X 0)).map_id,
      Category.id_comp, SingleZero.ι_termHom, SingleZero.ι_termHom_assoc,
      HomologicalComplex.single_map_f_self]
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      NatTrans.comp_app, NatTrans.comp_app]
    simp only [Category.assoc]
    rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, NatTrans.id_app, Category.comp_id]
  · have hz : IsZero (((curriedTensor (ModuleCat.{0} R)).obj
      ((SingleZero.singleZero R M).X i)).obj (K.X j)) :=
      (tensorRight (K.X j)).map_isZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)
    exact hz.eq_of_src _ _

def flatHomologyIso (M : ModuleCat.{0} R) [Module.Flat R M] (n : ℤ) :
    ((Homotopy.complexFunctor R K).obj (SingleZero.singleZero R M)).homology n ≅
      (tensorLeft M).obj (K.homology n) :=
  HomologicalComplex.homologyMapIso (SingleZero.iso R M K) n ≪≫
    (K.sc n).mapHomologyIso (tensorLeft M)

theorem flatHomologyIso_naturality [Module.Flat R M] [Module.Flat R N] (n : ℤ) :
    HomologicalComplex.homologyMap ((Homotopy.complexFunctor R K).map
      ((HomologicalComplex.single (ModuleCat.{0} R) (.up ℤ) 0).map f)) n ≫
        (flatHomologyIso R K N n).hom =
      (flatHomologyIso R K M n).hom ≫
        ((curriedTensor (ModuleCat.{0} R)).map f).app (K.homology n) := by
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n) (Naturality.naturality R K f)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  simp only [flatHomologyIso, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom]
  rw [← Category.assoc, h, Category.assoc]
  simp only [Category.assoc]
  congr 1
  change ShortComplex.homologyMap ((K.sc n).mapNatTrans ((curriedTensor (ModuleCat.{0} R)).map f)) ≫
    ((K.sc n).mapHomologyIso (tensorLeft N)).hom =
      ((K.sc n).mapHomologyIso (tensorLeft M)).hom ≫
        ((curriedTensor (ModuleCat.{0} R)).map f).app (K.sc n).homology
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

def moduleFunctor : ModuleCat.{0} R ⥤ CochainComplex (ModuleCat.{0} R) ℤ where
  obj M := ((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj K
  map f := (NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{0} R)).map f) (.up ℤ)).app K
  map_id M := by
    rw [CategoryTheory.Functor.map_id, NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
  map_comp f g := by
    rw [CategoryTheory.Functor.map_comp, NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]

def zeroNatIso :
    HomologicalComplex.single (ModuleCat.{0} R) (.up ℤ) 0 ⋙ Homotopy.complexFunctor R K ≅
      moduleFunctor R K :=
  NatIso.ofComponents (fun M => SingleZero.iso R M K) (fun f => Naturality.naturality R K f)

def degreeNatIso (d : ℤ) :
    CochainComplex.singleFunctor (ModuleCat.{0} R) d ⋙ Homotopy.complexFunctor R K ≅
      moduleFunctor R K ⋙ CategoryTheory.shiftFunctor _ (-d) :=
  CategoryTheory.Functor.isoWhiskerRight
    ((CochainComplex.singleFunctors (ModuleCat.{0} R)).shiftIso (-d) d 0 (neg_add_cancel d)).symm _ ≪≫
      CategoryTheory.Functor.associator _ _ _ ≪≫
      CategoryTheory.Functor.isoWhiskerLeft (CochainComplex.singleFunctor (ModuleCat.{0} R) 0)
        ((Homotopy.complexFunctor R K).commShiftIso (-d)) ≪≫
      (CategoryTheory.Functor.associator _ _ _).symm ≪≫
      CategoryTheory.Functor.isoWhiskerRight (zeroNatIso R K) _

theorem degreeNatIso_app (d : ℤ) (M : ModuleCat.{0} R) :
    (degreeNatIso R K d).app M = iso R M K d := by
  apply Iso.ext
  simp [degreeNatIso, zeroNatIso, iso]

theorem degree_naturality (d : ℤ) :
    (Homotopy.complexFunctor R K).map ((CochainComplex.singleFunctor (ModuleCat.{0} R) d).map f) ≫
      (iso R N K d).hom =
    (iso R M K d).hom ≫
      ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{0} R)).map f) (.up ℤ)).app K)⟦-d⟧' := by
  have h := (degreeNatIso R K d).hom.naturality f
  change _ ≫ ((degreeNatIso R K d).app N).hom = ((degreeNatIso R K d).app M).hom ≫ _ at h
  rw [degreeNatIso_app, degreeNatIso_app] at h
  exact h

theorem homology_naturality (d n : ℤ) :
    HomologicalComplex.homologyMap ((Homotopy.complexFunctor R K).map
      ((CochainComplex.singleFunctor (ModuleCat.{0} R) d).map f)) n ≫
        (homologyIso R N K d n).hom =
    (homologyIso R M K d n).hom ≫ HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{0} R)).map f) (.up ℤ)).app K) (n - d) := by
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n) (degree_naturality R K f d)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  have hs := (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{0} R) (-d) n (n - d) (by omega)).hom.naturality
    ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{0} R)).map f) (.up ℤ)).app K)
  simp only [homologyIso, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom]
  rw [← Category.assoc, h, Category.assoc]
  simp only [Category.assoc]
  congr 1

theorem flat_degree_naturality [Module.Flat R M] [Module.Flat R N] (d n : ℤ) :
    HomologicalComplex.homologyMap ((Homotopy.complexFunctor R K).map
      ((CochainComplex.singleFunctor (ModuleCat.{0} R) d).map f)) n ≫
        (TensorSingle.flatHomologyIso R N K d n).hom =
    (TensorSingle.flatHomologyIso R M K d n).hom ≫
      ((curriedTensor (ModuleCat.{0} R)).map f).app (K.homology (n - d)) := by
  simp only [TensorSingle.flatHomologyIso, Iso.trans_hom]
  rw [← Category.assoc, homology_naturality, Category.assoc]
  simp only [Category.assoc]
  congr 1
  change ShortComplex.homologyMap ((K.sc (n - d)).mapNatTrans ((curriedTensor (ModuleCat.{0} R)).map f)) ≫
    ((K.sc (n - d)).mapHomologyIso (tensorLeft N)).hom =
      ((K.sc (n - d)).mapHomologyIso (tensorLeft M)).hom ≫
        ((curriedTensor (ModuleCat.{0} R)).map f).app (K.sc (n - d)).homology
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Naturality

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.TensorSingle
