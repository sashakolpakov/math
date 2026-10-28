import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CanonicalSingularGlobalClasses
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularConstantCohomologyNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ComparisonHyperSquare
import OAI.AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison

/-! # Global Class Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.GlobalClassComparison

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # Actual smooth singular global classes compute original hypercohomology

Bijectivity follows from actual ordinary-to-smooth restriction and the original
canonical singular resolution; no new comparison or normalization is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open OAI.AlgebraicTopology.Singular
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Model" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "M" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X
local notation "Y" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)

set_option backward.isDefEq.respectTransparency false in
/-- The genuine original-atlas smooth-simplex restriction remains a quasi-isomorphism. -/
instance originalOrdinaryToSmoothAmbientInt_quasiIso :
    QuasiIso (Reference.OrdinarySmoothGlobalUnits.originalOrdinaryToSmoothAmbientInt X) := by
  have := AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison.quasiIso_manifoldSmoothCochainRestriction Model M
  dsimp only [Reference.OrdinarySmoothGlobalUnits.originalOrdinaryToSmoothAmbientInt, Reference.OrdinarySmoothGlobalUnits.originalOrdinaryToSmoothAmbientNat]
  infer_instance

/-- The actual smooth unit followed by the unchanged original global-to-hyper class map. -/
def originalSmoothAmbientHyperClass (n : ℤ) :
    (Reference.GlobalIntegrationClasses.originalManifoldSmoothCochainsInt X).homology n →+
      ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (Integration.originalSmoothSingularComplexInt X) n :=
  (GlobalNaturality.globalSectionsToHypercohomology X (Integration.originalSmoothSingularComplexInt X) n).comp
    (HomologicalComplex.homologyMap (Reference.GlobalIntegrationClasses.originalSmoothGlobalUnitInt X) n).hom

variable [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- The original canonical singular resolution comparison on actual ordinary integer classes. -/
def originalOrdinaryCanonicalSmoothHyperAddEquiv (n : ℕ) :
    (Reference.OrdinarySmoothGlobalUnits.originalOrdinaryAmbientCochainsInt X).homology (n : ℤ) ≃+
      ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (Integration.originalSmoothSingularComplexInt X) (n : ℤ) :=
  (Reference.CanonicalSingularGlobalClasses.originalOrdinaryAmbientIntegerCohomologyIso X n).addCommGroupIsoToAddEquiv.trans <|
    (SingularCochainBridge.singularCohomologyBridgeEquiv ℂ Y n).toAddEquiv.trans <|
    (Coefficient.SheafComparison.rawSingularHomologyIso ℂ Y n).symm.addCommGroupIsoToAddEquiv.trans <|
    (CanonicalSheafComparison.rawGlobalToSheafGlobalAddEquiv ℂ Y n).trans <|
    (CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv ℂ X n).trans <|
    Reference.SingularSmoothRestriction.originalSingularSmoothHypercohomologyAddEquiv X (n : ℤ)

/-- This canonical equivalence is exactly the genuine smooth-simplex restriction class. -/
theorem originalOrdinaryCanonicalSmoothHyperAddEquiv_apply (n : ℕ)
    (z : (Reference.OrdinarySmoothGlobalUnits.originalOrdinaryAmbientCochainsInt X).homology (n : ℤ)) :
    originalOrdinaryCanonicalSmoothHyperAddEquiv X n z =
      originalSmoothAmbientHyperClass X (n : ℤ)
        (HomologicalComplex.homologyMap (Reference.OrdinarySmoothGlobalUnits.originalOrdinaryToSmoothAmbientInt X) (n : ℤ) z) :=
  Reference.CanonicalSingularGlobalClasses.originalSmoothCanonicalSingular_hyperClass X n z

/-- Actual smooth ambient classes compute precisely the original smooth singular hyperclasses. -/
theorem originalSmoothAmbientHyperClass_bijective (n : ℕ) :
    Function.Bijective (originalSmoothAmbientHyperClass X (n : ℤ)) := by
  let r := HomologicalComplex.homologyMap (Reference.OrdinarySmoothGlobalUnits.originalOrdinaryToSmoothAmbientInt X) (n : ℤ)
  let e := originalOrdinaryCanonicalSmoothHyperAddEquiv X n
  have hr : Function.Bijective r :=
    (isoOfQuasiIsoAt (Reference.OrdinarySmoothGlobalUnits.originalOrdinaryToSmoothAmbientInt X) (n : ℤ)).addCommGroupIsoToAddEquiv.bijective
  constructor
  · intro a b hab
    obtain ⟨za, rfl⟩ := hr.2 a
    obtain ⟨zb, rfl⟩ := hr.2 b
    apply congrArg (fun z => r z)
    apply e.injective
    exact (originalOrdinaryCanonicalSmoothHyperAddEquiv_apply X n za).trans
      (hab.trans (originalOrdinaryCanonicalSmoothHyperAddEquiv_apply X n zb).symm)
  · intro a
    obtain ⟨z, hz⟩ := e.surjective a
    exact ⟨r z, (originalOrdinaryCanonicalSmoothHyperAddEquiv_apply X n z).symm.trans hz⟩

/-- The genuine smooth global-class equivalence has the actual original unit as its map. -/
def originalSmoothAmbientHyperAddEquiv (n : ℕ) :
    (Reference.GlobalIntegrationClasses.originalManifoldSmoothCochainsInt X).homology (n : ℤ) ≃+
      ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (Integration.originalSmoothSingularComplexInt X) (n : ℤ) :=
  AddEquiv.ofBijective (originalSmoothAmbientHyperClass X (n : ℤ))
    (originalSmoothAmbientHyperClass_bijective X n)

/-- Actual ordinary cohomology expressed in the original constant-sheaf cohomology. -/
def originalOrdinaryConstantCohomologyAddEquiv (n : ℕ) :
    (Reference.OrdinarySmoothGlobalUnits.originalOrdinaryAmbientCochainsInt X).homology (n : ℤ) ≃+ H^n(X; ℂ) :=
  (Reference.CanonicalSingularGlobalClasses.originalOrdinaryAmbientIntegerCohomologyIso X n).addCommGroupIsoToAddEquiv.trans <|
    (SingularCochainBridge.singularCohomologyBridgeEquiv ℂ Y n).toAddEquiv.trans <|
    (CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv ℂ X n).toAddEquiv

/-- The actual canonical smooth class retains the original constant-sheaf normalization. -/
theorem originalOrdinaryCanonicalSmoothHyperAddEquiv_constant (n : ℕ)
    (z : (Reference.OrdinarySmoothGlobalUnits.originalOrdinaryAmbientCochainsInt X).homology (n : ℤ)) :
    originalOrdinaryCanonicalSmoothHyperAddEquiv X n z =
      Reference.SingularSmoothRestriction.originalSingularSmoothHypercohomologyAddEquiv X (n : ℤ)
        (Coefficient.SheafComparison.constantHypercohomologySingularAddEquiv ℂ X n
          ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X n).symm
            (originalOrdinaryConstantCohomologyAddEquiv X n z))) := by
  have he := Reference.SingularConstantCohomologyNaturality.canonicalSingularToConstantSheafLinearEquiv_hypercohomology ℂ X n
    (SingularCochainBridge.singularCohomologyBridgeEquiv ℂ Y n
      ((Reference.CanonicalSingularGlobalClasses.originalOrdinaryAmbientIntegerCohomologyIso X n).hom z))
  have ht := congrArg (fun β => Reference.SingularSmoothRestriction.originalSingularSmoothHypercohomologyAddEquiv X (n : ℤ)
    (Coefficient.SheafComparison.constantHypercohomologySingularAddEquiv ℂ X n β)) he
  simpa only [AddEquiv.apply_symm_apply] using! ht.symm

/-- Original de Rham comparison and actual ordinary/smooth restriction give the same class. -/
theorem originalOrdinaryConstantDeRhamIntegration_hyperClass (n : ℕ)
    (z : (Reference.OrdinarySmoothGlobalUnits.originalOrdinaryAmbientCochainsInt X).homology (n : ℤ)) :
    Integration.originalSmoothIntegrationHypercohomologyAddEquiv X (n : ℤ)
        (Hypercohomology.originalDeRhamSmoothHypercohomologyAddEquiv X (n : ℤ)
          (ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X (n : ℤ)
            ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X n).symm
              (originalOrdinaryConstantCohomologyAddEquiv X n z)))) =
      originalSmoothAmbientHyperClass X (n : ℤ)
        (HomologicalComplex.homologyMap (Reference.OrdinarySmoothGlobalUnits.originalOrdinaryToSmoothAmbientInt X) (n : ℤ) z) := by
  rw [Reference.ComparisonHyperSquare.originalConstantComparisonHyperSquare]
  exact (originalOrdinaryCanonicalSmoothHyperAddEquiv_constant X n z).symm.trans
    (originalOrdinaryCanonicalSmoothHyperAddEquiv_apply X n z)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.GlobalClassComparison
