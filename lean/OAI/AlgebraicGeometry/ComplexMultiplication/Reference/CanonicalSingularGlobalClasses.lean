import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalUnits
import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSheafComparison

/-! # Canonical Singular Global Classes -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CanonicalSingularGlobalClasses

noncomputable section

/-! # The canonical original singular comparison has the genuine global-class normalization -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open OAI.AlgebraicTopology.Singular

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Y" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
local notation "F" => forget₂ (ModuleCat ℂ) AddCommGrpCat
local notation "K" => OAI.AlgebraicTopology.Cohomology.Singular.Basic.singularCochains
  (ModuleCat.of ℂ ℂ) (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
local notation "R" => OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex ℂ (TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))

/-- Canonical integer transport and scalar forgetting preserve actual native cohomology. -/
def originalOrdinaryAmbientIntegerCohomologyIso (n : ℕ) :
    (OrdinarySmoothGlobalUnits.originalOrdinaryAmbientCochainsInt X).homology (n : ℤ) ≅
      (F).obj (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) Y n) :=
  (OrdinarySmoothGlobalUnits.originalOrdinaryAmbientCochainsNat X).extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) rfl ≪≫
    ((K).sc n).mapHomologyIso (F)

omit [IsIntegral X.left] [Smooth X.hom] in
set_option backward.isDefEq.respectTransparency false in
/-- The actual raw bridge uses precisely chain evaluation on the actual native class. -/
theorem originalOrdinaryRawGlobalIntIso_homology_normalization (n : ℕ)
    (z : (OrdinarySmoothGlobalUnits.originalOrdinaryAmbientCochainsInt X).homology (n : ℤ)) :
    (((R).extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).hom)
        (HomologicalComplex.homologyMap (GlobalUnits.originalOrdinaryRawGlobalIntIso X).hom (n : ℤ) z) =
      (Coefficient.SheafComparison.rawSingularHomologyIso ℂ Y n).inv
        (SingularCochainBridge.singularCohomologyBridgeEquiv ℂ Y n
          ((originalOrdinaryAmbientIntegerCohomologyIso X n).hom z)) := by
  have he := ConcreteCategory.congr_hom
    (HomologicalComplex.extendHomologyIso_hom_naturality
      (IntrinsicReferenceGlobalCohomology.nativeSingularRawGlobalBridgeIso ℂ Y).hom ComplexShape.embeddingUpNat
        (j := n) (hj' := rfl)) z
  exact he.trans (IntrinsicReferenceGlobalCohomology.nativeSingularRawGlobalBridgeIso_homology_apply ℂ Y n _)

variable [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

set_option backward.isDefEq.respectTransparency false in
/-- The original canonical resolution comparison is the actual native ordinary global unit. -/
theorem originalOrdinaryCanonicalSingular_hyperClass (n : ℕ)
    (z : (OrdinarySmoothGlobalUnits.originalOrdinaryAmbientCochainsInt X).homology (n : ℤ)) :
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (SingularSmoothRestriction.originalOrdinarySingularComplexIntBridgeIso X).hom (n : ℤ)
        (GlobalNaturality.globalSectionsToHypercohomology X (SingularSmoothRestriction.originalOrdinarySingularComplexInt X) (n : ℤ)
          (HomologicalComplex.homologyMap (OrdinarySmoothGlobalUnits.originalOrdinaryGlobalUnitInt X) (n : ℤ) z)) =
      CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv ℂ X n
        (CanonicalSheafComparison.rawGlobalToSheafGlobalAddEquiv ℂ Y n
          ((Coefficient.SheafComparison.rawSingularHomologyIso ℂ Y n).inv
            (SingularCochainBridge.singularCohomologyBridgeEquiv ℂ Y n
              ((originalOrdinaryAmbientIntegerCohomologyIso X n).hom z)))) := by
  rw [GlobalUnits.originalOrdinaryRawGlobalUnit_hyperClass, GlobalUnits.originalRawSingularGlobalUnit_hyperClass,
    originalOrdinaryRawGlobalIntIso_homology_normalization]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The original canonical singular class restricts to the genuine integrated smooth class. -/
theorem originalSmoothCanonicalSingular_hyperClass (n : ℕ)
    (z : (OrdinarySmoothGlobalUnits.originalOrdinaryAmbientCochainsInt X).homology (n : ℤ)) :
    SingularSmoothRestriction.originalSingularSmoothHypercohomologyAddEquiv X (n : ℤ)
        (CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv ℂ X n
          (CanonicalSheafComparison.rawGlobalToSheafGlobalAddEquiv ℂ Y n
            ((Coefficient.SheafComparison.rawSingularHomologyIso ℂ Y n).inv
              (SingularCochainBridge.singularCohomologyBridgeEquiv ℂ Y n
                ((originalOrdinaryAmbientIntegerCohomologyIso X n).hom z))))) =
      GlobalNaturality.globalSectionsToHypercohomology X (ReferenceSmooth.Integration.originalSmoothSingularComplexInt X) (n : ℤ)
        (HomologicalComplex.homologyMap (GlobalIntegrationClasses.originalSmoothGlobalUnitInt X) (n : ℤ)
          (HomologicalComplex.homologyMap (OrdinarySmoothGlobalUnits.originalOrdinaryToSmoothAmbientInt X) (n : ℤ) z)) := by
  rw [← originalOrdinaryCanonicalSingular_hyperClass]
  change ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (SingularSmoothRestriction.originalSingularToSmoothSheafRestrictionInt X) (n : ℤ)
      (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (SingularSmoothRestriction.originalOrdinarySingularComplexIntBridgeIso X).hom (n : ℤ) _) = _
  rw [← ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply]
  have hb : (SingularSmoothRestriction.originalOrdinarySingularComplexIntBridgeIso X).hom ≫
      SingularSmoothRestriction.originalSingularToSmoothSheafRestrictionInt X =
    SingularSmoothRestriction.originalOrdinaryToSmoothSheafRestrictionInt X := by
    change (SingularSmoothRestriction.originalOrdinarySingularComplexIntBridgeIso X).hom ≫
      ((SingularSmoothRestriction.originalOrdinarySingularComplexIntBridgeIso X).inv ≫ _) = _
    rw [Iso.hom_inv_id_assoc]
  rw [hb]
  exact OrdinarySmoothGlobalUnits.originalOrdinarySmoothGlobalUnit_hyperClass X (n : ℤ) z

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CanonicalSingularGlobalClasses
