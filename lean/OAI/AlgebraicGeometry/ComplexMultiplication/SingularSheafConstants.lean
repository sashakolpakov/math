import OAI.AlgebraicGeometry.ComplexMultiplication.SingularSheafBridge
import OAI.AlgebraicGeometry.ComplexMultiplication.SingularPresheafConstants
import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.CanonicalConstants

/-! # Singular Sheaf Constants -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SingularSheafConstants

noncomputable section

/-! # Actual singular sheaf evaluation preserves the constant augmentation -/

open _root_.CategoryTheory _root_.TopologicalSpace _root_.AlgebraicGeometry ComplexPoint

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual module-sheaf augmentation retains the literal constant cochains. -/
theorem actualSingularConstantSheaf_unit (Y : TopCat.{0}) :
    toSheafify (Opens.grothendieckTopology Y)
        (AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantComplexPresheaf Y) ≫
      ((AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantSheafLocallyConstantIso Y).hom ≫
        AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation Y).hom =
      (AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantToLocallyConstant Y ≫
        AlgebraicTopology.Cohomology.Singular.Augmentation.Comparison.locallyConstantSingularAugmentation Y) ≫
          toSheafify (Opens.grothendieckTopology Y)
            (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℂ ℂ) Y 0) := by
  change toSheafify _ _ ≫
      ((AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantSheafLocallyConstantIso Y).hom.hom ≫
        (AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation Y).hom) = _
  rw [AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation_hom,
    ← Category.assoc, ← Category.assoc]
  exact congrArg (fun η =>
    (η ≫ AlgebraicTopology.Cohomology.Singular.Augmentation.Comparison.locallyConstantSingularAugmentation Y) ≫
      toSheafify (Opens.grothendieckTopology Y)
        (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℂ ℂ) Y 0))
    (AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantSheafLocallyConstantIso_fac Y)

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Y" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
local notation "J" => Opens.grothendieckTopology Y
local notation "F" => forget₂ (ModuleCat ℂ) AddCommGrpCat

omit [IsIntegral X.left] [Smooth X.hom] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original scalar sheaf and singular bridge retain the same genuine constant inclusion. -/
theorem originalSingularSheafBridge_constant :
    (ReferenceSmooth.CanonicalConstants.canonicalSmoothConstantSheafIso X).hom ≫
        (ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X).map
          ((AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantSheafLocallyConstantIso Y).hom ≫
            AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation Y) ≫
        (SingularSheafBridge.originalComplexSingularSheafBridgeIso Y).hom.f 0 =
      AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZeroSheaf ℂ Y := by
  apply CategoryTheory.Sheaf.hom_ext
  apply sheafify_hom_ext J _ _
    (AlgebraicTopology.Singular.SheafCochain.singularCochainSheaf ℂ Y 0).property
  change toSheafify J 𝓒ᵖ(Y; ℂ) ≫
      ((ReferenceSmooth.CanonicalConstants.canonicalSmoothConstantSheafIso X).hom.hom ≫
        Functor.whiskerRight
          ((AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantSheafLocallyConstantIso Y).hom ≫
            AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation Y).hom F ≫
        ((SingularSheafBridge.singularSheafComplexBridgeIso ℂ Y).hom.f 0).hom) = _
  rw [← Category.assoc, ← Category.assoc, ReferenceSmooth.CanonicalConstants.canonicalSmoothConstantSheafIso_unit,
    ← Functor.whiskerRight_comp, actualSingularConstantSheaf_unit,
    Functor.whiskerRight_comp, Category.assoc, SingularSheafBridge.singularSheafComplexBridgeIso_unit,
    ← Category.assoc, SingularPresheafConstants.singularPresheafBridge_constant]
  exact toSheafify_naturality J
    (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZero ℂ Y)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SingularSheafConstants
