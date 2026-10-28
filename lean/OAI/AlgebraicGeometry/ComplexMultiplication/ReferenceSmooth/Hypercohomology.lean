import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Augmentation
import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Integration
import OAI.AlgebraicGeometry.ComplexMultiplication.GlobalNaturality
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Hypercohomology -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Hypercohomology

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint
open scoped OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham.ComplexPoint

/-! # The original de Rham hypercohomology maps to actual smooth sheaf hypercohomology

The map is the extension by zero of the actual cotangent-form evaluation. It
retains the original constant augmentation and the original global class map.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint
open scoped ContDiff _root_.Manifold

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

/-- The original form evaluation, extended by zero in negative degrees. -/
def originalHolomorphicToSmoothSheafComplexInt :
    Ω•(X) ⟶ Integration.originalSmoothDeRhamComplexInt X :=
  HomologicalComplex.extendMap (FormSheaf.originalHolomorphicToSmoothSheafComplex X)
    ComplexShape.embeddingUpNat

/-- Actual evaluation induces cohomology isomorphisms in every integer degree. -/
instance originalHolomorphicToSmoothSheafComplexInt_quasiIso :
    QuasiIso (originalHolomorphicToSmoothSheafComplexInt X) := by
  have := Augmentation.originalHolomorphicToSmoothSheafComplex_quasiIso X
  exact (HomologicalComplex.quasiIso_extendMap_iff
    (FormSheaf.originalHolomorphicToSmoothSheafComplex X) ComplexShape.embeddingUpNat).2 inferInstance

/-- The extended evaluation retains the original actual constant augmentation. -/
theorem originalHolomorphicToSmoothSheafComplexInt_constant :
    ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X ≫
        originalHolomorphicToSmoothSheafComplexInt X =
      HomologicalComplex.extendMap (Augmentation.originalSmoothDeRhamAugmentation X)
        ComplexShape.embeddingUpNat := by
  change HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _ = _
  rw [← HomologicalComplex.extendMap_comp, Augmentation.originalHolomorphicToSmoothSheafComplex_constant]

/-- The unchanged original de Rham hypercohomology agrees with actual smooth sheaf hypercohomology. -/
def originalDeRhamSmoothHypercohomologyAddEquiv (n : ℤ) :
    H_dR^n(X) ≃+ ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (Integration.originalSmoothDeRhamComplexInt X) n where
  toEquiv := Localization.SmallShiftedHom.postcompEquiv
    (originalHolomorphicToSmoothSheafComplexInt X)
    (originalHolomorphicToSmoothSheafComplexInt_quasiIso X)
  map_add' := (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (originalHolomorphicToSmoothSheafComplexInt X) n).map_add

/-- The actual hypercohomology equivalence is the original postcomposition map. -/
theorem originalDeRhamSmoothHypercohomologyAddEquiv_apply (n : ℤ) (α : H_dR^n(X)) :
    originalDeRhamSmoothHypercohomologyAddEquiv X n α =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (originalHolomorphicToSmoothSheafComplexInt X) n α := rfl

/-- Actual global holomorphic-form classes map to their actual smooth-form classes. -/
theorem originalDeRhamSmoothHypercohomology_globalClass (n : ℤ)
    (z : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) Ω•(X)).homology n) :
    originalDeRhamSmoothHypercohomologyAddEquiv X n
        (GlobalNaturality.globalSectionsToHypercohomology X Ω•(X) n z) =
      GlobalNaturality.globalSectionsToHypercohomology X (Integration.originalSmoothDeRhamComplexInt X) n
        (HomologicalComplex.homologyMap
          (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).mapHomologicalComplex ℤᵘᵖ).map
              (originalHolomorphicToSmoothSheafComplexInt X)) n z) :=
  (GlobalNaturality.globalSectionsToHypercohomology_naturality X
    (originalHolomorphicToSmoothSheafComplexInt X) n z).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Hypercohomology
