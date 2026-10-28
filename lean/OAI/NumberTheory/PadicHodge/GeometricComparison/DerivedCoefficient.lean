import OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedResolution

/-! # Derived Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedCoefficient.DerivedCoefficientTransport

noncomputable section

/-! The coefficient-adjusted exact-functor map is the actual shifted-Hom transport. -/

open _root_.CategoryTheory Limits

universe u u' v w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (A : C) (B : D) (e : F.obj A ≅ B)

theorem map_eq_transport {K : CochainComplex C ℤ} {L : CochainComplex D ℤ}
    (a : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L) (n : ℤ)
    (x : (DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :
    (DerivedCategory.singleFunctor D 0).map e.inv ≫
      AcyclicExact.AcyclicExactFunctorNaturality.derivedMap F A a n x =
      AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport F.mapDerivedCategory
        (((F.mapDerivedCategorySingleFunctor 0).app A) ≪≫
          (DerivedCategory.singleFunctor D 0).mapIso e) (AlgebraicGeometry.Comparison.Betti.Derived.ResolutionNaturality.Ext.derivedComplexMap F a) x := by
  rw [DerivedResolution.DerivedResolutionExactNaturality.map_eq_transport]
  simp only [AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport, Iso.trans_inv, Functor.mapIso_inv, Category.assoc]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedCoefficient.DerivedCoefficientTransport
