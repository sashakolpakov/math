import OAI.AlgebraicGeometry.Comparison.Betti.SingleCocycleFunctor

/-! # Cocycle Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Derived.CocycleFunctor.Ext

noncomputable section

/-! Derived inverse image preserves the actual shifted cocycle representatives. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe w w' u u' v v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X : C} {K : CochainComplex C ℤ} {n : ℤ}

theorem singleCocycleHom_derived_map (f : X ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0) :
    (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      (ShiftedHom.map (ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom f hf) DerivedCategory.Q)
        F.mapDerivedCategory) ≫ (F.mapDerivedCategoryFactors.hom.app K)⟦n⟧' =
    ShiftedHom.map
      (SingleCocycleFunctor.Ext.singleCocycleHom (K := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (F.map f) (by change F.map f ≫ F.map (K.d n (n + 1)) = 0; rw [← F.map_comp, hf, F.map_zero]))
      DerivedCategory.Q := by
  let P := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let c := SingleCocycleFunctor.Ext.singleCocycleHom f hf
  have h : (ShiftedHom.map (ShiftedHom.map c DerivedCategory.Q) F.mapDerivedCategory) ≫
      (F.mapDerivedCategoryFactors.hom.app K)⟦n⟧' =
    F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X) ≫
      ShiftedHom.map (ShiftedHom.map c P) DerivedCategory.Q := by
    have h' := ShiftedHom.map_naturality c F.mapDerivedCategoryFactors.hom
    simpa only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_map] using h'
  erw [h, ← Category.assoc,
    F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
  have hc := congrArg (fun k => ShiftedHom.map k (DerivedCategory.Q (C := D)))
    (SingleCocycleFunctor.Ext.singleCocycleHom_map F f hf)
  have hm : ShiftedHom.map
      ((F.mapCochainComplexSingleFunctor 0).inv.app X ≫ ShiftedHom.map c P) DerivedCategory.Q =
    DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app X) ≫
      ShiftedHom.map (ShiftedHom.map c P) DerivedCategory.Q := by
    dsimp only [ShiftedHom.map]
    erw [DerivedCategory.Q.map_comp ((F.mapCochainComplexSingleFunctor 0).inv.app X)
      (P.map c ≫ (P.commShiftIso n).hom.app K)]
    exact Category.assoc _ _ _
  exact hm.symm.trans hc

end

end OAI.AlgebraicGeometry.Comparison.Betti.Derived.CocycleFunctor.Ext
