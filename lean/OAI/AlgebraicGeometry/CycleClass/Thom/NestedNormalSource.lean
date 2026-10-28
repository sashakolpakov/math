import OAI.AlgebraicGeometry.CycleClass.Thom.NestedNormalEquation
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.RetractionComparison

/-! # Nested Normal Source -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NestedNormalSource.Constructions.Class

noncomputable section

/-! The constructed source equation represents the restriction of the
inner immersion's actual canonical Thom class. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions
  NestedNormalEquation.Constructions Normal.RetractionComparison.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (C : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.sourceManifold Z) q) (z : C.regularAnalyticSpace)
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ) Z.regularComplementInclusion
    (C.regularComplementInclusion z))
  (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair C.regularAnalyticModel (Fin q → ℂ) C.regularComplementInclusion z)
  (hPQ : Z.regularComplementInclusion ⁻¹' P.neighborhood ⊆ Q.neighborhood)

theorem parameterSource_mapsTo :
    Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion Z.regularAnalyticSpace
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding : Set Z.regularAnalyticSpace))
      (Normal.RetractionComparison.Constructions.sourceEquationOpen Z (C.regularComplementInclusion z) P (NestedNormalEquation.Constructions.parameter Z C z P Q hPQ) :
        Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)) (Set.range C.regularComplementInclusion)ᶜ := by
  intro y hy hC
  exact hy ((NestedNormalEquation.Constructions.parameter_zero_iff Z C z P Q hPQ y).mpr hC)

theorem parameterInclusion_mapsTo :
    Set.MapsTo (NestedNormalEquation.Constructions.parameterInclusion Z C z P Q hPQ)
      (Normal.RetractionComparison.Constructions.sourceEquationOpen Z (C.regularComplementInclusion z) P (NestedNormalEquation.Constructions.parameter Z C z P Q hPQ) :
        Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)) Q.relativeComplement := by
  intro y hy
  exact parameterSource_mapsTo Z C z P Q hPQ hy

theorem sourceThomClass_eq_parameter
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, Z.regularAnalyticModel)
      𝓘(ℂ, C.regularAnalyticModel × (Fin q → ℂ))) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion Z.regularAnalyticSpace
        (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding : Set Z.regularAnalyticSpace))
      (parameterSource_mapsTo Z C z P Q hPQ) (2 * q) C.regularThomClass =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NestedNormalEquation.Constructions.parameter Z C z P Q hPQ)
      (A := (Normal.RetractionComparison.Constructions.sourceEquationOpen Z (C.regularComplementInclusion z) P (NestedNormalEquation.Constructions.parameter Z C z P Q hPQ) :
        Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding))) (B := {0}ᶜ)
      (fun _ hx => hx) (2 * q) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q) := by
  have hs := C.regularThomClass_restrict_normalPair z Q hQ
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (NestedNormalEquation.Constructions.parameterInclusion Z C z P Q hPQ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion Z.regularAnalyticSpace Q.neighborhood)
      (parameterInclusion_mapsTo Z C z P Q hPQ)
      (A := (Normal.RetractionComparison.Constructions.sourceEquationOpen Z (C.regularComplementInclusion z) P (NestedNormalEquation.Constructions.parameter Z C z P Q hPQ) :
        Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)))
      (B := Q.relativeComplement) (C := (Set.range C.regularComplementInclusion)ᶜ)
      (fun _ hx => hx) (2 * q)) C.regularThomClass
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NestedNormalEquation.Constructions.parameterInclusion Z C z P Q hPQ)
      (parameterInclusion_mapsTo Z C z P Q hPQ) (2 * q)
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) Z.regularAnalyticSpace
        (Set.range C.regularComplementInclusion)ᶜ Q.openNeighborhood (2 * q) C.regularThomClass) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion Z.regularAnalyticSpace
        (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding : Set Z.regularAnalyticSpace))
      (parameterSource_mapsTo Z C z P Q hPQ) (2 * q) C.regularThomClass at hc
  rw [hs] at hc
  apply hc.symm.trans
  exact ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (NestedNormalEquation.Constructions.parameterInclusion Z C z P Q hPQ)
      Q.normalCoordinate (parameterInclusion_mapsTo Z C z P Q hPQ) Q.normalCoordinate_mapsTo (2 * q))
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NestedNormalSource.Constructions.Class
