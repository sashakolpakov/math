import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.CanonicalConstants
import OAI.AlgebraicGeometry.ComplexMultiplication.SheafAnyHomology

/-! # Augmentation -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Augmentation

noncomputable section

/-! # The original holomorphic-to-smooth sheaf map is a quasi-isomorphism

Both actual de Rham complexes resolve the same scalar constant sheaf. The map
retains those actual constant augmentations, so it induces the cohomology
isomorphisms of sheaf complexes without an assumed comparison diagram.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Model" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "F" => OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X
local notation "C" => OAI.Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexSheafOn (TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
local notation "mapComplex" =>
  Functor.mapHomologicalComplex (FormSheaf.originalSmoothFormSheafForget X) (ComplexShape.up ℕ)

/-- The genuine constant-sheaf isomorphism in degree-zero cochain complexes. -/
def originalSmoothConstantComplexIso :
    (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))).obj
        𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ≅
      (mapComplex).obj
        ((CochainComplex.single₀ (TopCat.Sheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))).obj C) :=
  (CochainComplex.single₀ _).mapIso (CanonicalConstants.canonicalSmoothConstantSheafIso X) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).symm.app C

/-- The actual smooth de Rham augmentation with the original scalar coefficient object. -/
def originalSmoothDeRhamAugmentation :=
  (originalSmoothConstantComplexIso X).hom ≫
    (mapComplex).map (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldDeRhamSheafAugmentation Model (ComplexPoint.Basic.ComplexSchemePoint X))

set_option backward.isDefEq.respectTransparency false in
/-- The actual smooth scalar augmentation remains a quasi-isomorphism after forgetting scalars. -/
theorem originalSmoothDeRhamAugmentation_quasiIso :
    QuasiIso (originalSmoothDeRhamAugmentation X) := by
  let := Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldDeRhamSheafAugmentation_quasiIso Model (ComplexPoint.Basic.ComplexSchemePoint X)
  dsimp only [originalSmoothDeRhamAugmentation]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The smooth augmentation retains the actual scalar inclusion as its degree-zero map. -/
theorem originalSmoothDeRhamAugmentation_f_zero :
    (originalSmoothDeRhamAugmentation X).f 0 =
      (CanonicalConstants.canonicalSmoothConstantSheafIso X).hom ≫
        (F).map (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldConstantToDeRham Model (ComplexPoint.Basic.ComplexSchemePoint X)) := by
  simp only [originalSmoothDeRhamAugmentation, HomologicalComplex.comp_f, Functor.mapIso_hom,
    Functor.mapHomologicalComplex_map_f, originalSmoothConstantComplexIso,
    Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq, Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldDeRhamSheafAugmentation,
    CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  change (((𝟙 _ ≫ (CanonicalConstants.canonicalSmoothConstantSheafIso X).hom ≫ 𝟙 _) ≫
      𝟙 _ ≫ (F).map (𝟙 _)) ≫ (F).map
        (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldConstantToDeRham Model (ComplexPoint.Basic.ComplexSchemePoint X))) = _
  simp

/-- The original holomorphic-to-smooth map retains the genuine constant augmentation. -/
theorem originalHolomorphicToSmoothSheafComplex_constant :
    ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) ≫
        FormSheaf.originalHolomorphicToSmoothSheafComplex X = originalSmoothDeRhamAugmentation X := by
  apply HomologicalComplex.from_single_hom_ext
  change (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X (Topology.Dimension.Basic.TopologicalSpace.dim X.left)).f 0 ≫
    FormSheaf.originalHolomorphicToSmoothSheaf X 0 = (originalSmoothDeRhamAugmentation X).f 0
  rw [originalSmoothDeRhamAugmentation_f_zero]
  change ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) ≫
    FormSheaf.originalHolomorphicToSmoothSheaf X 0 = _
  exact CanonicalConstants.originalHolomorphicToSmoothSheaf_canonicalConstant X

/-- The actual original holomorphic-to-smooth sheaf-complex map induces cohomology isomorphisms. -/
theorem originalHolomorphicToSmoothSheafComplex_quasiIso :
    QuasiIso (FormSheaf.originalHolomorphicToSmoothSheafComplex X) := by
  have : QuasiIso (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X (Topology.Dimension.Basic.TopologicalSpace.dim X.left)) := inferInstance
  have : QuasiIso (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) ≫
      FormSheaf.originalHolomorphicToSmoothSheafComplex X) := by
    rw [originalHolomorphicToSmoothSheafComplex_constant]
    exact originalSmoothDeRhamAugmentation_quasiIso X
  exact quasiIso_of_comp_left (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X (Topology.Dimension.Basic.TopologicalSpace.dim X.left))
    (FormSheaf.originalHolomorphicToSmoothSheafComplex X)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Augmentation
