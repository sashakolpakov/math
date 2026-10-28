import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularConstant
import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Hypercohomology

/-! # Comparison Hyper Square -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ComparisonHyperSquare

noncomputable section

section

/-! # The original Betti and de Rham constant comparison square

Both original constant augmentations give the same genuine smooth-singular
augmentation. The proof uses actual restriction and actual simplex integration.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Model" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "Y" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
local notation "F" => OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X
local notation "mapComplex" => Functor.mapHomologicalComplex
  (ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X) (ComplexShape.up ℕ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Genuine singular restriction preserves the full original constant augmentation. -/
theorem originalOrdinarySingularConstantAugmentation_restriction :
    SingularConstant.originalOrdinarySingularConstantAugmentation X ≫
        (mapComplex).map (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction Model
          (ComplexPoint.Basic.ComplexSchemePoint X) (ModuleCat.of ℂ ℂ)) =
      (ReferenceSmooth.Augmentation.originalSmoothConstantComplexIso X).hom ≫
        (mapComplex).map (SmoothIntegrationGlobalValues.actualSmoothSingularConstantAugmentation Model (ComplexPoint.Basic.ComplexSchemePoint X)) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    SingularConstant.originalOrdinarySingularConstantAugmentation,
    CochainComplex.fromSingle₀Equiv_symm_apply_f_zero,
    SingularConstant.originalSmoothConstantComplexIso_hom_f_zero,
    SmoothIntegrationGlobalValues.actualSmoothSingularConstantAugmentation,
    HomologicalComplex.single_map_f_self,
    AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafResolutionMap_f_zero]
  rw [Category.assoc, ← Functor.map_comp, Category.assoc,
    ← AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothSheafAugmentation_eq_singular_comp]
  simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unchanged original singular augmentation gives the genuine smooth augmentation. -/
theorem originalSingularConstantAugmentation_restriction :
    AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex ℂ Y ≫
        (SingularSheafBridge.originalComplexSingularSheafBridgeIso Y).inv ≫
        (mapComplex).map (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction Model
          (ComplexPoint.Basic.ComplexSchemePoint X) (ModuleCat.of ℂ ℂ)) =
      (ReferenceSmooth.Augmentation.originalSmoothConstantComplexIso X).hom ≫
        (mapComplex).map (SmoothIntegrationGlobalValues.actualSmoothSingularConstantAugmentation Model (ComplexPoint.Basic.ComplexSchemePoint X)) := by
  rw [← SingularConstant.originalOrdinarySingularConstantAugmentation_bridge X]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact originalOrdinarySingularConstantAugmentation_restriction X

/-- The same actual smooth-singular augmentation, extended by zero in negative degrees. -/
def originalSmoothSingularConstantAugmentationInt :
    ComplexPoint.Basic.ComplexSchemePoint.constantCoefficientSheafComplexInt X ℂ ⟶ ReferenceSmooth.Integration.originalSmoothSingularComplexInt X :=
  HomologicalComplex.extendMap
    ((ReferenceSmooth.Augmentation.originalSmoothConstantComplexIso X).hom ≫
      (mapComplex).map (SmoothIntegrationGlobalValues.actualSmoothSingularConstantAugmentation Model (ComplexPoint.Basic.ComplexSchemePoint X)))
    ComplexShape.embeddingUpNat

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full original integer-indexed singular constant augmentation is retained. -/
theorem originalSingularConstantAugmentationInt_restriction :
    ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X ℂ ≫
        SingularSmoothRestriction.originalSingularToSmoothSheafRestrictionInt X =
      originalSmoothSingularConstantAugmentationInt X := by
  change HomologicalComplex.extendMap _ _ ≫
    (HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _) = _
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
  exact congrArg (fun f => HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)
    (originalSingularConstantAugmentation_restriction X)

/-- Actual integration gives precisely the same original integer-indexed augmentation. -/
theorem originalHolomorphicConstantAugmentationInt_integration :
    ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X ≫
        ReferenceSmooth.Hypercohomology.originalHolomorphicToSmoothSheafComplexInt X ≫
        ReferenceSmooth.Integration.originalSmoothIntegrationSheafComplexInt X =
      originalSmoothSingularConstantAugmentationInt X := by
  rw [← Category.assoc, ReferenceSmooth.Hypercohomology.originalHolomorphicToSmoothSheafComplexInt_constant]
  change HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _ = _
  rw [← HomologicalComplex.extendMap_comp]
  exact congrArg (fun f => HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)
    (SingularConstant.originalSmoothDeRhamAugmentation_integration X)

/-- Both unchanged original constant comparison maps give the same actual smooth-singular map. -/
theorem originalConstantComparisonSquare :
    ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X ≫
        ReferenceSmooth.Hypercohomology.originalHolomorphicToSmoothSheafComplexInt X ≫
        ReferenceSmooth.Integration.originalSmoothIntegrationSheafComplexInt X =
      ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X ℂ ≫
        SingularSmoothRestriction.originalSingularToSmoothSheafRestrictionInt X := by
  rw [originalHolomorphicConstantAugmentationInt_integration,
    originalSingularConstantAugmentationInt_restriction]

end

/-! # The unchanged original comparison agrees with actual smooth integration

The square on original complexes induces the same square on actual
hypercohomology, in every integer degree.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual smooth simplex integration retains the unchanged original de Rham comparison. -/
theorem originalConstantComparisonHyperSquare (n : ℤ)
    (β : ComplexPoint.Basic.ComplexSchemePoint.ComplexConstantCohomology X n) :
    ReferenceSmooth.Integration.originalSmoothIntegrationHypercohomologyAddEquiv X n
        (ReferenceSmooth.Hypercohomology.originalDeRhamSmoothHypercohomologyAddEquiv X n
          (ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n β)) =
      SingularSmoothRestriction.originalSingularSmoothHypercohomologyAddEquiv X n
        (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X ℂ) n β) := by
  change ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X _ n (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X _ n
    (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X _ n β)) = ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X _ n
      (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X _ n β)
  rw [← ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply, ← ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply,
    originalConstantComparisonSquare, ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply]

/-- The inverse actual integration identifies precisely the original de Rham class. -/
theorem originalConstantComparisonSmoothClass (n : ℤ)
    (β : ComplexPoint.Basic.ComplexSchemePoint.ComplexConstantCohomology X n) :
    ReferenceSmooth.Hypercohomology.originalDeRhamSmoothHypercohomologyAddEquiv X n
        (ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n β) =
      (ReferenceSmooth.Integration.originalSmoothIntegrationHypercohomologyAddEquiv X n).symm
        (SingularSmoothRestriction.originalSingularSmoothHypercohomologyAddEquiv X n
          (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X ℂ) n β)) := by
  apply (ReferenceSmooth.Integration.originalSmoothIntegrationHypercohomologyAddEquiv X n).injective
  rw [AddEquiv.apply_symm_apply, originalConstantComparisonHyperSquare]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ComparisonHyperSquare
