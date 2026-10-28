import OAI.AlgebraicGeometry.Comparison.Betti.Derived.CocycleFunctor
import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.HomNaturality

/-! # Cocycle -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Derived.Cocycle.Ext

noncomputable section

/-! Actual shifted cocycles retain coefficient precomposition and exact-functor comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w u' v' w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem derivedSingleCocycle_precomp {A A' : C} {K : CochainComplex C ℤ} {n : ℤ}
    (v : A' ⟶ A) (z : A ⟶ K.X n) (hz : z ≫ K.d n (n + 1) = 0) :
    ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom (v ≫ z)
      (by rw [Category.assoc, hz, comp_zero])) DerivedCategory.Q =
      (DerivedCategory.singleFunctor C 0).map v ≫
        ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom z hz) DerivedCategory.Q := by
  rw [ResolutionCocycleNaturality.Ext.singleCocycleHom_precomp]
  dsimp only [ShiftedHom.map]
  erw [Functor.map_comp]
  exact Category.assoc _ _ _

variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

theorem derivedSingleCocycle_functor_postcomp {A : C}
    {K : CochainComplex C ℤ} {L : CochainComplex D ℤ} {n : ℤ}
    (z : A ⟶ K.X n) (hz : z ≫ K.d n (n + 1) = 0)
    (β : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L) :
    (F.mapDerivedCategorySingleFunctor 0).inv.app A ≫
      ShiftedHom.map (ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom z hz) DerivedCategory.Q)
        F.mapDerivedCategory ≫
      (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map β)⟦n⟧' =
    ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom (F.map z ≫ β.f n)
      (by
        erw [Category.assoc, β.comm, ← Category.assoc]
        change (F.map z ≫ F.map (K.d n (n + 1))) ≫ β.f (n + 1) = 0
        rw [← F.map_comp, hz, F.map_zero]
        exact zero_comp)) DerivedCategory.Q := by
  have hzF : F.map z ≫ ((F.mapHomologicalComplex (.up ℤ)).obj K).d n (n + 1) = 0 := by
    change F.map z ≫ F.map (K.d n (n + 1)) = 0
    rw [← F.map_comp, hz, F.map_zero]
  have hF := CocycleFunctor.Ext.singleCocycleHom_derived_map F z hz
  have hβ := Acyclic.HomNaturality.Ext.derivedSingleCocycle_postcomp (F.map z) hzF β
  rw [Functor.map_comp]
  let u := (F.mapDerivedCategorySingleFunctor 0).inv.app A
  let v := ShiftedHom.map (ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom z hz) DerivedCategory.Q)
    F.mapDerivedCategory
  let c := (F.mapDerivedCategoryFactors.hom.app K)⟦n⟧'
  let d := (DerivedCategory.Q.map β)⟦n⟧'
  exact (congrArg (u ≫ ·) (Category.assoc v c d).symm).trans
    ((Category.assoc u (v ≫ c) d).symm.trans
      ((congrArg (· ≫ d) hF).trans hβ.symm))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Derived.Cocycle.Ext
