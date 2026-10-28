import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Single Cocycle Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SingleCocycleFunctor.Ext

noncomputable section

/-! Actual cocycle representatives commute with additive functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CochainComplex _root_.CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Abelian C]
  {D : Type*} [Category* D] [Abelian D]
  {X : C} {K : CochainComplex C ℤ} {n : ℤ}

def singleCocycleHom (f : X ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0) :
    (CochainComplex.singleFunctor C 0).obj X ⟶ K⟦n⟧ :=
  Cocycle.equivHomShift.symm (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)

theorem singleCocycleHom_f_zero (f : X ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0) :
    (singleCocycleHom f hf).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom ≫ f ≫
        (K.shiftFunctorObjXIso n 0 n (zero_add n).symm).inv := by
  simp [singleCocycleHom, Cocycle.equivHomShift_symm_apply, Cochain.rightShift_v]

variable (F : C ⥤ D) [F.Additive]

theorem singleCocycleHom_map (f : X ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0) :
    (F.mapCochainComplexSingleFunctor 0).inv.app X ≫
        ShiftedHom.map (singleCocycleHom f hf) (F.mapHomologicalComplex (ComplexShape.up ℤ)) =
      singleCocycleHom (K := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (F.map f) (by change F.map f ≫ F.map (K.d n (n + 1)) = 0; rw [← F.map_comp, hf, F.map_zero]) := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i = 0
  · subst i
    simp only [ShiftedHom.map, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
    erw [Category.comp_id, singleCocycleHom_f_zero f hf,
      singleCocycleHom_f_zero (K := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) (F.map f)]
    erw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X
    have hc : F.map e.inv ≫ F.map e.hom = 𝟙 (F.obj X) :=
      (F.map_comp e.inv e.hom).symm.trans
        ((F.congr_map e.inv_hom_id).trans (F.map_id X))
    erw [F.map_comp e.hom (f ≫ (K.shiftFunctorObjXIso n 0 n (zero_add n).symm).inv),
      Category.assoc, ← Category.assoc (F.map e.inv) (F.map e.hom), hc, Category.id_comp,
      F.map_comp f (K.shiftFunctorObjXIso n 0 n (zero_add n).symm).inv]
    congr 2
    simp [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]
    exact eqToHom_map F _
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (F.obj X) i hi).eq_of_src _ _

end

end OAI.AlgebraicGeometry.Comparison.Betti.SingleCocycleFunctor.Ext
