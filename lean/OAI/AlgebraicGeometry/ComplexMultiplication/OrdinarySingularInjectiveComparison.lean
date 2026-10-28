import OAI.AlgebraicGeometry.ComplexMultiplication.OpenGlobalSingularNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedInjectiveGlobalSquare

/-! # Ordinary Singular Injective Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.OrdinarySingularInjectiveComparison

noncomputable section

/-! # The ordinary canonical comparison uses the actual injective augmentation -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits _root_.TopologicalSpace _root_.HomologicalComplex
open _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

omit [Foundations.ProjectiveSpaceIs.IsProjective X.hom] in
theorem originalSingularInjective_augmentation :
    ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X ℚ ≫
      AlgebraicTopology.Support.SingularFlasqueModel.Singular.singularToConstantInjectiveComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
        (ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X) = ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveAugmentation X := by
  change extendMap (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex ℚ
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) ComplexShape.embeddingUpNat ≫
      extendMap (AlgebraicTopology.Support.SingularFlasqueModel.Singular.singularToConstantInjectiveResolution (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
        (ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X)) ComplexShape.embeddingUpNat = _
  rw [← HomologicalComplex.extendMap_comp, AlgebraicTopology.Support.SingularFlasqueModel.Singular.constants_comp_singularToConstantInjectiveResolution]
  rfl

theorem ordinarySingularInjective_comparison (n : ℕ)
    (a : (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).homology n) :
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveAugmentation X) (n : ℤ)
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm
        (CanonicalSheafComparison.canonicalSingularToConstantSheafAddEquiv ℚ X n
          ((Coefficient.SheafComparison.rawSingularHomologyIso ℚ (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n).hom a))) =
    GlobalNaturality.globalSectionsToHypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X) (n : ℤ)
      (homologyMap
        (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).mapHomologicalComplex ℤᵘᵖ).map
          (AlgebraicTopology.Support.SingularFlasqueModel.Singular.singularToConstantInjectiveComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
            (ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X))) (n : ℤ)
        ((Coefficient.SheafComparison.singularGlobalIntegerHomologyIso ℚ X n).inv
          (homologyMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex ℚ
            (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) n a))) := by
  let r := (Coefficient.SheafComparison.rawSingularHomologyIso ℚ (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n).addCommGroupIsoToAddEquiv
  let t := CanonicalSheafComparison.rawGlobalToSheafGlobalAddEquiv ℚ (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n
  let g := CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv ℚ X n
  let s := Coefficient.SheafComparison.constantHypercohomologySingularAddEquiv ℚ X n
  let c := ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n
  have hc : s (c.symm (CanonicalSheafComparison.canonicalSingularToConstantSheafAddEquiv ℚ X n (r a))) =
      g (t a) := by
    change s (c.symm (c (s.symm (g (t (r.symm (r a))))))) = _
    rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
  rw [← originalSingularInjective_augmentation X, ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply]
  change ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X _ (n : ℤ)
    (s (c.symm (CanonicalSheafComparison.canonicalSingularToConstantSheafAddEquiv ℚ X n (r a)))) = _
  rw [hc]
  exact (GlobalNaturality.globalSectionsToHypercohomology_naturality X
    (AlgebraicTopology.Support.SingularFlasqueModel.Singular.singularToConstantInjectiveComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      (ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X)) (n : ℤ) _).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.OrdinarySingularInjectiveComparison
