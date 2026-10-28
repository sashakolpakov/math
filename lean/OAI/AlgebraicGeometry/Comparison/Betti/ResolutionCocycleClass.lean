import OAI.AlgebraicGeometry.Comparison.Betti.Derived.ResolutionFunctor

/-! # Resolution Cocycle Class -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ResolutionCocycleClass.Ext

noncomputable section

/-! Derived cohomology classes formed from actual resolution cocycles. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe w w' u u' v v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  {X Y : C} {K : CochainComplex C ℤ} {n : ℤ}

def resolutionCocycleHom (a : (CochainComplex.singleFunctor C 0).obj Y ⟶ K) [QuasiIso a]
    (f : X ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0) :
    (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧ := by
  let Q : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  have ha : IsIso (Q.map a) := (DerivedCategory.isIso_Q_map_iff_quasiIso C a).mpr inferInstance
  exact ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom f hf) Q ≫
    (@CategoryTheory.inv _ _ _ _ (Q.map a) ha)⟦n⟧'

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

theorem resolutionCocycleHom_map (a : (CochainComplex.singleFunctor C 0).obj Y ⟶ K) [QuasiIso a]
    (f : X ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0) :
    (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      ShiftedHom.map (resolutionCocycleHom a f hf) F.mapDerivedCategory ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦n⟧' =
      resolutionCocycleHom (Derived.ResolutionFunctor.Ext.mappedAugmentation F a) (F.map f)
        (by change F.map f ≫ F.map (K.d n (n + 1)) = 0; rw [← F.map_comp, hf, F.map_zero]) := by
  let c := ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom f hf) (DerivedCategory.Q (C := C))
  let q := inv (DerivedCategory.Q.map a)
  let S := shiftFunctor (DerivedCategory D) n
  have hm : ShiftedHom.map (c ≫ q⟦n⟧') F.mapDerivedCategory =
      ShiftedHom.map c F.mapDerivedCategory ≫ (F.mapDerivedCategory.map q)⟦n⟧' := by
    have h := ShiftedHom.map_comp c (ShiftedHom.mk₀ (0 : ℤ) rfl q) (zero_add n) F.mapDerivedCategory
    simpa only [ShiftedHom.comp_mk₀, ShiftedHom.map_mk₀] using h
  change (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
    ShiftedHom.map (c ≫ q⟦n⟧') F.mapDerivedCategory ≫
      S.map ((F.mapDerivedCategorySingleFunctor 0).hom.app Y) = _
  erw [hm, Category.assoc (ShiftedHom.map c F.mapDerivedCategory)
    (S.map (F.mapDerivedCategory.map q)) (S.map ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)),
    ← S.map_comp (F.mapDerivedCategory.map q)
    ((F.mapDerivedCategorySingleFunctor 0).hom.app Y), Derived.ResolutionFunctor.Ext.mappedAugmentation_derived_inverse,
    S.map_comp]
  erw [← Category.assoc (ShiftedHom.map c F.mapDerivedCategory)
    (S.map (F.mapDerivedCategoryFactors.hom.app K))
      (S.map (inv (DerivedCategory.Q.map (Derived.ResolutionFunctor.Ext.mappedAugmentation F a)))),
    ← Category.assoc ((F.mapDerivedCategorySingleFunctor 0).inv.app X)
      (ShiftedHom.map c F.mapDerivedCategory ≫ S.map (F.mapDerivedCategoryFactors.hom.app K))
      (S.map (inv (DerivedCategory.Q.map (Derived.ResolutionFunctor.Ext.mappedAugmentation F a)))),
    Derived.CocycleFunctor.Ext.singleCocycleHom_derived_map F f hf]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.ResolutionCocycleClass.Ext
