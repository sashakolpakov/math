import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.CocycleNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.HomNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.CocycleFunctor

/-! # Acyclic Exact -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AcyclicExact.AcyclicExactFunctorNaturality

noncomputable section

/-! The actual acyclic hypercohomology comparison commutes with exact functors and maps of complexes. -/

open _root_.CategoryTheory Limits Abelian Opposite

universe u u' v w w' z z'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [HasDerivedCategory.{z} C]
  {D : Type u'} [Category.{v} D] [Abelian D] [HasExt.{w'} D] [HasDerivedCategory.{z'} D]
  (F : C ⥤ D) [F.Additive] (A : C)
  {K : CochainComplex C ℤ} {L : CochainComplex D ℤ}
  (φ : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L)

def complexMap : AlgebraicGeometry.Comparison.Betti.IntegerAcyclicHomComplex.Ext.integerHomComplex A K ⟶ AlgebraicGeometry.Comparison.Betti.IntegerAcyclicHomComplex.Ext.integerHomComplex (F.obj A) L where
  f n := AddCommGrpCat.ofHom
    ((Preadditive.rightComp (F.obj A) (φ.f n)).comp (F.mapAddHom (X := A) (Y := K.X n)))
  comm' n m _ := by
    ext a
    change (F.map a ≫ φ.f n) ≫ L.d n m = F.map (a ≫ K.d n m) ≫ φ.f m
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => F.map a ≫ k) (φ.comm n m)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ φ.f m) (F.map_comp a (K.d n m)).symm)))

omit [HasExt C] [HasDerivedCategory C] [HasExt D] [HasDerivedCategory D] in
theorem closed (n : ℤ) (a : A ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    (F.map a ≫ φ.f n) ≫ L.d n (n + 1) = 0 :=
  AlgebraicGeometry.Comparison.Betti.AbCochainClasses.Homology.map_closed n (complexMap F A φ) a ha

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

def derivedMap (n : ℤ)
    (a : (DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :
    (DerivedCategory.singleFunctor D 0).obj (F.obj A) ⟶ (DerivedCategory.Q.obj L)⟦n⟧ :=
  ((F.mapDerivedCategorySingleFunctor 0).inv.app A ≫ ShiftedHom.map a F.mapDerivedCategory ≫
    (F.mapDerivedCategoryFactors.hom.app K)⟦n⟧') ≫ (DerivedCategory.Q.map φ)⟦n⟧'

omit [HasExt C] [HasExt D] in
theorem derivedMap_class (n : ℤ) (a : A ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    derivedMap F A φ n (ShiftedHom.map (AlgebraicGeometry.Comparison.Betti.SingleCocycleFunctor.Ext.singleCocycleHom a ha) DerivedCategory.Q) =
      ShiftedHom.map (AlgebraicGeometry.Comparison.Betti.SingleCocycleFunctor.Ext.singleCocycleHom (F.map a ≫ φ.f n) (closed F A φ n a ha))
        DerivedCategory.Q := by
  have hF : F.map a ≫ ((F.mapHomologicalComplex (.up ℤ)).obj K).d n (n + 1) = 0 := by
    change F.map a ≫ F.map (K.d n (n + 1)) = 0
    rw [← F.map_comp, ha, F.map_zero]
  exact (congrArg (fun k : (DerivedCategory.singleFunctor D 0).obj (F.obj A) ⟶
      (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K))⟦n⟧ =>
        k ≫ (DerivedCategory.Q.map φ)⟦n⟧')
    (AlgebraicGeometry.Comparison.Betti.Derived.CocycleFunctor.Ext.singleCocycleHom_derived_map F a ha)).trans
      (AlgebraicGeometry.Comparison.Betti.Acyclic.HomNaturality.Ext.derivedSingleCocycle_postcomp (K := (F.mapHomologicalComplex (.up ℤ)).obj K)
        (L := L) (n := n) (F.map a) hF φ).symm

variable [EnoughInjectives C] [EnoughInjectives D]

theorem naturality (b c : ℤ) [K.IsStrictlyGE b] [L.IsStrictlyGE c]
    (hK : ∀ p q, Subsingleton (Ext.{w} A (K.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext.{w'} (F.obj A) (L.X p) (q + 1)))
    (n : ℤ) (x : (AlgebraicGeometry.Comparison.Betti.IntegerAcyclicHomComplex.Ext.integerHomComplex A K).homology n) :
    AlgebraicGeometry.Comparison.Betti.Acyclic.HomDerived.Ext.acyclicHomCohomologyDerivedEquiv (F.obj A) L c hL n
      (HomologicalComplex.homologyMap (complexMap F A φ) n x) =
      derivedMap F A φ n (AlgebraicGeometry.Comparison.Betti.Acyclic.HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A K b hK n x) := by
  obtain ⟨a, ha, rfl⟩ := AlgebraicGeometry.Comparison.Betti.AbCochainClasses.Homology.cochainClass_surjective (AlgebraicGeometry.Comparison.Betti.IntegerAcyclicHomComplex.Ext.integerHomComplex A K) n x
  change A ⟶ K.X n at a
  change a ≫ K.d n (n + 1) = 0 at ha
  have h₁ := congrArg (AlgebraicGeometry.Comparison.Betti.Acyclic.HomDerived.Ext.acyclicHomCohomologyDerivedEquiv (F.obj A) L c hL n)
    (AlgebraicGeometry.Comparison.Betti.AbCochainClasses.Homology.cochainClass_naturality n (complexMap F A φ) a ha)
  have h₂ := AlgebraicGeometry.Comparison.Betti.Acyclic.CocycleNormalization.Ext.acyclicHomCohomologyDerivedEquiv_class (F.obj A) L c hL n
    (F.map a ≫ φ.f n) (AlgebraicGeometry.Comparison.Betti.AbCochainClasses.Homology.map_closed n (complexMap F A φ) a ha)
  have h₃ := (derivedMap_class F A φ n a ha).symm
  have h₄ := congrArg (derivedMap F A φ n)
    (AlgebraicGeometry.Comparison.Betti.Acyclic.CocycleNormalization.Ext.acyclicHomCohomologyDerivedEquiv_class A K b hK n a ha).symm
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AcyclicExact.AcyclicExactFunctorNaturality
