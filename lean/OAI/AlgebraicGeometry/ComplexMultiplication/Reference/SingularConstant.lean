import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularSmoothRestriction
import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Augmentation

/-! # Singular Constant -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularConstant

noncomputable section

/-! # The actual constant augmentations agree as original sheaf complexes -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Model" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "Y" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
local notation "F" => OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X
local notation "mapComplex" => Functor.mapHomologicalComplex
  (ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X) (ComplexShape.up ℕ)

omit [IsIntegral X.left] [Smooth X.hom] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual constant-complex comparison retains the scalar inclusion in degree zero. -/
theorem originalSmoothConstantComplexIso_hom_f_zero :
    (ReferenceSmooth.Augmentation.originalSmoothConstantComplexIso X).hom.f 0 =
      (ReferenceSmooth.CanonicalConstants.canonicalSmoothConstantSheafIso X).hom := by
  simp only [ReferenceSmooth.Augmentation.originalSmoothConstantComplexIso, Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.comp_f, Iso.app_hom, Iso.symm_hom,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq]
  change (𝟙 _ ≫ (ReferenceSmooth.CanonicalConstants.canonicalSmoothConstantSheafIso X).hom ≫ 𝟙 _) ≫
    𝟙 _ ≫ (F).map (𝟙 _) = _
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine ordinary singular augmentation with the unchanged original scalar object. -/
def originalOrdinarySingularConstantAugmentation :
    (CochainComplex.single₀ (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)).obj 𝓒(Y; ℂ) ⟶
      (mapComplex).obj (AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex Y) :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨(ReferenceSmooth.CanonicalConstants.canonicalSmoothConstantSheafIso X).hom ≫
      (F).map ((AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantSheafLocallyConstantIso Y).hom ≫
        AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation Y), by
      rw [Functor.mapHomologicalComplex_obj_d, Category.assoc, ← Functor.map_comp,
        Category.assoc, AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation_d,
        Limits.comp_zero, Functor.map_zero, Limits.comp_zero]⟩

omit [IsIntegral X.left] [Smooth X.hom] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual chain evaluation identifies the full unchanged constant-augmentation complexes. -/
theorem originalOrdinarySingularConstantAugmentation_bridge :
    originalOrdinarySingularConstantAugmentation X ≫
        (SingularSheafBridge.originalComplexSingularSheafBridgeIso Y).hom =
      AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex ℂ Y := by
  apply HomologicalComplex.from_single_hom_ext
  change (originalOrdinarySingularConstantAugmentation X).f 0 ≫
    (SingularSheafBridge.originalComplexSingularSheafBridgeIso Y).hom.f 0 = _
  rw [originalOrdinarySingularConstantAugmentation,
    CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  exact SingularSheafConstants.originalSingularSheafBridge_constant X

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Genuine integration retains the actual smooth constant augmentation as complexes. -/
theorem originalSmoothDeRhamAugmentation_integration :
    ReferenceSmooth.Augmentation.originalSmoothDeRhamAugmentation X ≫
        (mapComplex).map (SmoothIntegrationGlobalValues.actualSmoothIntegrationSheaf Model (ComplexPoint.Basic.ComplexSchemePoint X)) =
      (ReferenceSmooth.Augmentation.originalSmoothConstantComplexIso X).hom ≫
        (mapComplex).map (SmoothIntegrationGlobalValues.actualSmoothSingularConstantAugmentation Model (ComplexPoint.Basic.ComplexSchemePoint X)) := by
  dsimp only [ReferenceSmooth.Augmentation.originalSmoothDeRhamAugmentation]
  rw [Category.assoc, ← Functor.map_comp, SmoothIntegrationGlobalValues.actualSmoothIntegrationSheaf_constant]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularConstant
