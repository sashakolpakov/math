import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Constants
import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.ScalarForget
import OAI.AlgebraicGeometry.ComplexMultiplication.ScalarForgettingSheafification

/-! # Canonical Constants -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.CanonicalConstants

noncomputable section

/-! # The actual smooth constant augmentation under canonical scalar forgetting

The comparison is the genuine canonical sheafification isomorphism. Its unit
identifies the original scalar inclusion with the actual smooth constant forms.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Model" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "J" => Opens.grothendieckTopology (TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
local notation "P" => OAI.AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantComplexPresheaf (TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
local notation "forgetComplex" => forget₂ (ModuleCat ℂ) AddCommGrpCat

set_option backward.isDefEq.respectTransparency false in
/-- The original coefficient sheaf is the actual underlying smooth coefficient sheaf. -/
def canonicalSmoothConstantSheafIso :
    𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ≅
      (FormSheaf.originalSmoothFormSheafForget X).obj
        (Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexSheafOn (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) :=
  (ScalarForgettingSheafification.scalarSheafificationCanonicalIso ℂ (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).app P

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The coefficient comparison retains the genuine presheaf unit. -/
theorem canonicalSmoothConstantSheafIso_unit :
    toSheafify J 𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ≫
      (canonicalSmoothConstantSheafIso X).hom.hom =
        Functor.whiskerRight (toSheafify J P) forgetComplex :=
  ScalarForgettingSheafification.scalarSheafificationCanonicalIso_unit ℂ (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) P

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual smooth constants have the original scalar values. -/
theorem canonicalSmoothConstantToZero_unit :
    toSheafify J 𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ≫
      ((canonicalSmoothConstantSheafIso X).hom ≫
        (FormSheaf.originalSmoothFormSheafForget X).map
          (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldConstantToDeRham Model (ComplexPoint.Basic.ComplexSchemePoint X))).hom =
      Constants.originalConstantsToSmoothZero X := by
  change toSheafify J 𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ≫
    ((canonicalSmoothConstantSheafIso X).hom.hom ≫
      Functor.whiskerRight (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldConstantToDeRham Model (ComplexPoint.Basic.ComplexSchemePoint X)).hom
        forgetComplex) = _
  calc
    _ = Functor.whiskerRight (toSheafify J P) forgetComplex ≫
        Functor.whiskerRight (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldConstantToDeRham Model (ComplexPoint.Basic.ComplexSchemePoint X)).hom
          forgetComplex :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun η => η ≫
          Functor.whiskerRight (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldConstantToDeRham Model (ComplexPoint.Basic.ComplexSchemePoint X)).hom
            forgetComplex) (canonicalSmoothConstantSheafIso_unit X))
    _ = _ := by
      change Functor.whiskerRight (toSheafify J P) forgetComplex ≫
        Functor.whiskerRight
          ((AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantSheafLocallyConstantIso
              (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).hom.hom ≫
            (Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf Model (ComplexPoint.Basic.ComplexSchemePoint X)).hom)
          forgetComplex = _
      rw [← Functor.whiskerRight_comp, ← Category.assoc,
        AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantSheafLocallyConstantIso_fac]
      rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original holomorphic form evaluation preserves the actual constant sheaf augmentation. -/
theorem originalHolomorphicToSmoothSheaf_canonicalConstant :
    ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) ≫
        FormSheaf.originalHolomorphicToSmoothSheaf X 0 =
      (canonicalSmoothConstantSheafIso X).hom ≫
        (FormSheaf.originalSmoothFormSheafForget X).map
          (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldConstantToDeRham Model (ComplexPoint.Basic.ComplexSchemePoint X)) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (FormSheaf.originalSmoothFormAddSheaf X 0).property
  calc
    _ = ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) ≫
        FormSheaf.originalHolomorphicToSmoothPresheaf X 0 :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun η => η ≫ (FormSheaf.originalHolomorphicToSmoothSheaf X 0).hom)
          (toSheafify_naturality J (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X (Topology.Dimension.Basic.TopologicalSpace.dim X.left))).symm).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun η => ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) ≫ η)
                (FormSheaf.originalHolomorphicToSmoothSheaf_unit X 0))))
    _ = Constants.originalConstantsToSmoothZero X := Constants.originalHolomorphicToSmoothPresheaf_constant X
    _ = _ := (canonicalSmoothConstantToZero_unit X).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.CanonicalConstants
