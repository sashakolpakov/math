import OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafScalarChange
import OAI.NumberTheory.PadicHodge.PeriodInvariants.SheafCoefficients
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension

/-! # Sheaf Scalar Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SheafScalarChange.SectionScalarChange

noncomputable section

/-! The native coefficient-change comparison after sheafification and extension by zero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {R S : Type} [Field R] [Field S] (σ : R ≃+* S)
  (X : Over (Spec (CommRingCat.of S)))

abbrev sheafRestriction : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves S X ⥤
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X) :=
  sheafCompose (Opens.grothendieckTopology X.left) (ModuleCat.restrictScalars σ.toRingHom)

instance sheafRestriction_equivalence : (sheafRestriction σ X).IsEquivalence :=
  PeriodInvariants.SheafCoefficients.compose_equivalence (Opens.grothendieckTopology X.left)
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ)

instance sheafRestriction_additive : (sheafRestriction σ X).Additive where
  map_add := by intros; rfl

instance restriction_preservesSheafification :
    (Opens.grothendieckTopology X.left).PreservesSheafification
      (ModuleCat.restrictScalars σ.toRingHom) :=
  Sheaf.preservesSheafification_of_adjunction (Opens.grothendieckTopology X.left)
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).toAdjunction

def sheafComplexIso :
    ((sheafRestriction σ X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex S X) ≅
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X) :=
  ((NatIso.mapHomologicalComplex
      (sheafComposeNatIso (Opens.grothendieckTopology X.left)
        (ModuleCat.restrictScalars σ.toRingHom)
        (sheafificationAdjunction _ (ModuleCat S))
        (sheafificationAdjunction _ (ModuleCat R))).symm (ComplexShape.up ℕ)).app
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S X)) ≪≫
    ((presheafToSheaf (Opens.grothendieckTopology X.left)
      (ModuleCat R)).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
        (PresheafScalarChange.SectionScalarChange.presheafComplexIso σ X).symm

def sheafComplexIntIso :
    ((sheafRestriction σ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt S X) ≅
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X) :=
  AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso (sheafRestriction σ X) ComplexShape.embeddingUpNat
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex S X) ≪≫
      (ComplexShape.embeddingUpNat.extendFunctor
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X))).mapIso (sheafComplexIso σ X)

def coefficientSheafIso :
    (sheafRestriction σ X).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf S X) ≅
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X) :=
  (constantCommuteCompose (Opens.grothendieckTopology X.left)
    (ModuleCat.restrictScalars σ.toRingHom)).app (ModuleCat.of S S) ≪≫
      (constantSheaf (Opens.grothendieckTopology X.left) (ModuleCat R)).mapIso
        (ModuleCat.restrictScalarsIsoOfEquiv σ)

theorem sheafRestriction_map_smul
    {P Q : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves S X} (f : P ⟶ Q) (s : S) :
    (sheafRestriction σ X).map (s • f) = σ.symm s • (sheafRestriction σ X).map f := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change s • f.hom.app U x = σ (σ.symm s) • f.hom.app U x
  rw [σ.apply_symm_apply]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SheafScalarChange.SectionScalarChange
