import OAI.AlgebraicGeometry.Comparison.Betti.HomFunctor

/-! # Functor Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.FunctorNaturality.Ext

noncomputable section

/-! The acyclic Hom calculation intertwines the actual coefficient comparison with the normalized derived functor map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe u u' v w w' e e'

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{e} C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v} D] [Abelian D] [EnoughInjectives D]
  [HasExt.{e'} D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (A : C) (A' : D) (a : A' ⟶ F.obj A)
  (K : CochainComplex C ℤ) (L : CochainComplex D ℤ)
  (b c : ℤ) [K.IsStrictlyGE b] [L.IsStrictlyGE c]

theorem acyclicHomCohomologyDerivedEquiv_functor
    (hK : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext A' (L.X p) (q + 1)))
    (β : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
    (n : ℤ) (x : (IntegerAcyclicHomComplex.Ext.integerHomComplex A K).homology n) :
    HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A' L c hL n
      (HomologicalComplex.homologyMap (HomFunctor.Ext.integerHomFunctorComparison F a β) n x) =
      (DerivedCategory.singleFunctor D 0).map a ≫
        (F.mapDerivedCategorySingleFunctor 0).inv.app A ≫
          ShiftedHom.map (HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A K b hK n x) F.mapDerivedCategory ≫
            (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map β)⟦n⟧' := by
  obtain ⟨z, hz, rfl⟩ := AbCochainClasses.Homology.cochainClass_surjective (IntegerAcyclicHomComplex.Ext.integerHomComplex A K) n x
  change A ⟶ K.X n at z
  change z ≫ K.d n (n + 1) = 0 at hz
  let H := HomFunctor.Ext.integerHomFunctorComparison F a β
  have hzβ : (F.map z ≫ β.f n) ≫ L.d n (n + 1) = 0 := by
    erw [Category.assoc, β.comm, ← Category.assoc]
    change (F.map z ≫ F.map (K.d n (n + 1))) ≫ β.f (n + 1) = 0
    rw [← F.map_comp, hz, F.map_zero]
    exact zero_comp
  have hza : (a ≫ F.map z ≫ β.f n) ≫ L.d n (n + 1) = 0 :=
    (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) hzβ).trans comp_zero)
  have hc := (congrArg (HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A' L c hL n)
    (AbCochainClasses.Homology.cochainClass_naturality n H z hz)).trans
      (CocycleNormalization.Ext.acyclicHomCohomologyDerivedEquiv_class A' L c hL n (a ≫ F.map z ≫ β.f n) hza)
  have hp := Derived.Cocycle.Ext.derivedSingleCocycle_precomp a (F.map z ≫ β.f n) hzβ
  have hF := Derived.Cocycle.Ext.derivedSingleCocycle_functor_postcomp F z hz β
  have hs := CocycleNormalization.Ext.acyclicHomCohomologyDerivedEquiv_class A K b hK n z hz
  exact hc.trans (hp.trans ((congrArg ((DerivedCategory.singleFunctor D 0).map a ≫ ·) hF.symm).trans
    (congrArg (fun t => (DerivedCategory.singleFunctor D 0).map a ≫
      (F.mapDerivedCategorySingleFunctor 0).inv.app A ≫ ShiftedHom.map t F.mapDerivedCategory ≫
        (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map β)⟦n⟧') hs.symm)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.FunctorNaturality.Ext
