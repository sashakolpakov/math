import OAI.AlgebraicGeometry.Comparison.Betti.Derived.CocycleFunctor

/-! # Resolution Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Derived.ResolutionFunctor.Ext

noncomputable section

/-! The actual inverse of a resolution augmentation is compatible with exact functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe w w' u u' v v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {Y : C} {K : CochainComplex C ℤ}

def mappedAugmentation (a : (CochainComplex.singleFunctor C 0).obj Y ⟶ K) :
    (CochainComplex.singleFunctor D 0).obj (F.obj Y) ⟶
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  (F.mapCochainComplexSingleFunctor 0).inv.app Y ≫
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map a

instance mappedAugmentation_quasiIso (a : (CochainComplex.singleFunctor C 0).obj Y ⟶ K)
    [QuasiIso a] : QuasiIso (mappedAugmentation F a) := by
  have h : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map a) := inferInstance
  exact quasiIso_comp _ _ (hφ' := h)

theorem mappedAugmentation_derived_square
    (a : (CochainComplex.singleFunctor C 0).obj Y ⟶ K) :
    F.mapDerivedCategory.map (DerivedCategory.Q.map a) ≫ F.mapDerivedCategoryFactors.hom.app K =
      (F.mapDerivedCategorySingleFunctor 0).hom.app Y ≫ DerivedCategory.Q.map (mappedAugmentation F a) := by
  apply ((F.mapDerivedCategorySingleFunctor 0).app Y).inv_comp_eq.mp
  erw [F.mapDerivedCategoryFactors_hom_naturality a, ← Category.assoc,
    F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
  exact (DerivedCategory.Q.map_comp ((F.mapCochainComplexSingleFunctor 0).inv.app Y)
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map a)).symm

theorem mappedAugmentation_derived_inverse
    (a : (CochainComplex.singleFunctor C 0).obj Y ⟶ K) [QuasiIso a] :
    F.mapDerivedCategory.map (inv (DerivedCategory.Q.map a)) ≫
        (F.mapDerivedCategorySingleFunctor 0).hom.app Y =
      F.mapDerivedCategoryFactors.hom.app K ≫ inv (DerivedCategory.Q.map (mappedAugmentation F a)) := by
  have : IsIso (DerivedCategory.Q.map a) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C a).mpr inferInstance
  have : IsIso (DerivedCategory.Q.map (mappedAugmentation F a)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso D _).mpr inferInstance
  erw [Functor.map_inv, IsIso.inv_comp_eq, ← Category.assoc, mappedAugmentation_derived_square,
    Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Derived.ResolutionFunctor.Ext
