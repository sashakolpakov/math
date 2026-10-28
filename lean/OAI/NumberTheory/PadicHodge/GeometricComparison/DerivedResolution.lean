import OAI.NumberTheory.PadicHodge.GeometricComparison.AcyclicExact
import OAI.NumberTheory.PadicHodge.GeometricComparison.ShiftedInverse
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.ResolutionNaturality

/-! # Derived Resolution -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedResolution.DerivedResolutionExactNaturality

noncomputable section

/-! Actual quasi-isomorphism resolutions commute with the derived maps of exact functors. -/

open _root_.CategoryTheory Limits OAI.AlgebraicGeometry.Comparison.Betti.Derived.ResolutionNaturality.Ext

universe u u' v w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

theorem square {K K' : CochainComplex C ℤ} {L L' : CochainComplex D ℤ}
    (f : K ⟶ K') (g : L ⟶ L')
    (a : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
    (b : (F.mapHomologicalComplex (.up ℤ)).obj K' ⟶ L')
    (h : (F.mapHomologicalComplex (.up ℤ)).map f ≫ b = a ≫ g) :
    F.mapDerivedCategory.map (DerivedCategory.Q.map f) ≫ AlgebraicGeometry.Comparison.Betti.Derived.ResolutionNaturality.Ext.derivedComplexMap F b =
      AlgebraicGeometry.Comparison.Betti.Derived.ResolutionNaturality.Ext.derivedComplexMap F a ≫ DerivedCategory.Q.map g := by
  let Q : CochainComplex D ℤ ⥤ DerivedCategory D := DerivedCategory.Q
  have h₁ := F.mapDerivedCategoryFactors_hom_naturality f
  have h₂ := (Q.map_comp ((F.mapHomologicalComplex (.up ℤ)).map f) b).symm.trans
    ((congrArg Q.map h).trans (Q.map_comp a g))
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

variable (A : C)

theorem map_eq_transport {K : CochainComplex C ℤ} {L : CochainComplex D ℤ}
    (a : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L) (n : ℤ)
    (x : (DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :
    AcyclicExact.AcyclicExactFunctorNaturality.derivedMap F A a n x =
      AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport F.mapDerivedCategory ((F.mapDerivedCategorySingleFunctor 0).app A)
        (AlgebraicGeometry.Comparison.Betti.Derived.ResolutionNaturality.Ext.derivedComplexMap F a) x := by
  dsimp only [AcyclicExact.AcyclicExactFunctorNaturality.derivedMap, AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport, AlgebraicGeometry.Comparison.Betti.Derived.ResolutionNaturality.Ext.derivedComplexMap]
  rw [(shiftFunctor (DerivedCategory D) n).map_comp]
  simp only [Category.assoc]
  rfl

theorem naturality {K K' : CochainComplex C ℤ} {L L' : CochainComplex D ℤ}
    (f : K ⟶ K') (g : L ⟶ L') [QuasiIso f] [QuasiIso g]
    (a : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
    (b : (F.mapHomologicalComplex (.up ℤ)).obj K' ⟶ L')
    (h : (F.mapHomologicalComplex (.up ℤ)).map f ≫ b = a ≫ g)
    (n : ℤ) (x : (DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj K')⟦n⟧) :
    AcyclicExact.AcyclicExactFunctorNaturality.derivedMap F A b n x ≫ (inv (DerivedCategory.Q.map g))⟦n⟧' =
      AcyclicExact.AcyclicExactFunctorNaturality.derivedMap F A a n (x ≫ (inv (DerivedCategory.Q.map f))⟦n⟧') := by
  rw [map_eq_transport, map_eq_transport]
  exact ShiftedInverse.ShiftedInverseTransport.naturality F.mapDerivedCategory ((F.mapDerivedCategorySingleFunctor 0).app A)
    (asIso (DerivedCategory.Q.map f)) (asIso (DerivedCategory.Q.map g))
    (AlgebraicGeometry.Comparison.Betti.Derived.ResolutionNaturality.Ext.derivedComplexMap F a) (AlgebraicGeometry.Comparison.Betti.Derived.ResolutionNaturality.Ext.derivedComplexMap F b) (square F f g a b h) n x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedResolution.DerivedResolutionExactNaturality
