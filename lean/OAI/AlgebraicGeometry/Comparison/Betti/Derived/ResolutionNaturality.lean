import OAI.AlgebraicGeometry.Comparison.Betti.Derived.ResolutionFunctor

/-! # Resolution Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Derived.ResolutionNaturality.Ext

noncomputable section

/-! A normalized augmentation square remains a square after exact derived inverse image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe w w' u u' v v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

def derivedComplexMap {K : CochainComplex C ℤ} {L : CochainComplex D ℤ}
    (g : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L) :
    F.mapDerivedCategory.obj (DerivedCategory.Q.obj K) ⟶ DerivedCategory.Q.obj L :=
  F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map g

theorem derived_augmentation_square {Y : C} {Z : D}
    {K : CochainComplex C ℤ} {L : CochainComplex D ℤ}
    (a : (CochainComplex.singleFunctor C 0).obj Y ⟶ K)
    (b : (CochainComplex.singleFunctor D 0).obj Z ⟶ L)
    (g : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L)
    (u : F.obj Y ⟶ Z)
    (h : ResolutionFunctor.Ext.mappedAugmentation F a ≫ g = (CochainComplex.singleFunctor D 0).map u ≫ b) :
    F.mapDerivedCategory.map (DerivedCategory.Q.map a) ≫ derivedComplexMap F g =
      (F.mapDerivedCategorySingleFunctor 0).hom.app Y ≫
        (DerivedCategory.singleFunctor D 0).map u ≫ DerivedCategory.Q.map b := by
  let Q : CochainComplex D ℤ ⥤ DerivedCategory D := DerivedCategory.Q
  have hh : Q.map (ResolutionFunctor.Ext.mappedAugmentation F a) ≫ Q.map g =
      Q.map ((CochainComplex.singleFunctor D 0).map u) ≫ Q.map b :=
    (Q.map_comp _ _).symm.trans ((Q.congr_map h).trans (Q.map_comp _ _))
  change F.mapDerivedCategory.map (DerivedCategory.Q.map a) ≫
      (F.mapDerivedCategoryFactors.hom.app K ≫ Q.map g) = _
  erw [← Category.assoc, ResolutionFunctor.Ext.mappedAugmentation_derived_square F a, Category.assoc, hh]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Derived.ResolutionNaturality.Ext
