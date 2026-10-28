import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafScalarChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearDerivedQ
import OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedEquivalenceIs

/-! # Scalar Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarChange.SectionScalarChange

noncomputable section

/-! The actual semilinear change of coefficients on de Rham hypercohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R S : Type} [Field R] [Field S] (σ : R ≃+* S)
  (X : Over (Spec (CommRingCat.of S)))

instance derivedRestriction_equivalence : (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapDerivedCategory.IsEquivalence := by
  let e := (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).asEquivalence
  let : e.functor.Additive := SheafScalarChange.SectionScalarChange.sheafRestriction_additive σ X
  exact DerivedEquivalenceIs.DerivedEquivalence.induced_isEquivalence e

def derivedCoefficientIso :
    (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves S X) 0).obj
          (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf S X)) ≅
      (DerivedCategory.singleFunctor
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X)) 0).obj
          (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X)) := by
  refine ((SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapDerivedCategorySingleFunctor 0).app
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf S X) ≪≫ ?_
  change (DerivedCategory.singleFunctor _ 0).obj
      ((SheafScalarChange.SectionScalarChange.sheafRestriction σ X).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf S X)) ≅ _
  exact (DerivedCategory.singleFunctor _ 0).mapIso (SheafScalarChange.SectionScalarChange.coefficientSheafIso σ X)

def derivedComplexIso :
    (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt S X)) ≅
      DerivedCategory.Q.obj
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X)) :=
  (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapDerivedCategoryFactors.app
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt S X) ≪≫
    DerivedCategory.Q.mapIso (SheafScalarChange.SectionScalarChange.sheafComplexIntIso σ X)

def derivedShiftedComplexIso (n : ℤ) :
    (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapDerivedCategory.obj
        ((DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt S X))⟦n⟧) ≅
      (DerivedCategory.Q.obj
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X)))⟦n⟧ :=
  ((SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapDerivedCategory.commShiftIso n).app
      (DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt S X)) ≪≫
    (shiftFunctor _ n).mapIso (derivedComplexIso σ X)

def cohomologyEquiv (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology S X n ≃ₛₗ[σ.symm.toRingHom]
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X) n :=
  (SemilinearDerivedQ.SemilinearDerived.homEquiv σ.symm (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapDerivedCategory
    (SemilinearDerivedQ.SemilinearDerived.derived_scalar_identity σ.symm.toRingHom (SheafScalarChange.SectionScalarChange.sheafRestriction σ X)
      (fun Y s => (SheafScalarChange.SectionScalarChange.sheafRestriction_map_smul σ X (𝟙 Y) s).trans
        (congrArg (fun f => σ.symm s • f) ((SheafScalarChange.SectionScalarChange.sheafRestriction σ X).map_id Y)))) _ _).trans
    (Linear.homCongr R (derivedCoefficientIso σ X) (derivedShiftedComplexIso σ X n))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarChange.SectionScalarChange
