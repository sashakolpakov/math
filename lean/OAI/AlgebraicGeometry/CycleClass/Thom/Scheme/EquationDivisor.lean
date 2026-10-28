import OAI.AlgebraicGeometry.CycleClass.Thom.WindingNormalization
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrincipalDivisorComparison

/-! # Equation Divisor -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.EquationDivisor.Constructions

noncomputable section

/-! An actual equation agreeing with a rational function on its unit
open pulls the normalized origin class back to the finite supported
divisor sum with the original algebraic orders. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.PrincipalBoundary OAI.AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.BoundaryNaturality OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions
  RationalBoundary.Constructions.Restriction PrincipalDivisorComparison.Constructions
  SupportedPrincipalDivisor.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  {g : X.left.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left g) (hg : g ≠ 0)

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

include hg

theorem equation_eq_principalDivisorSupportedClass
    (A : Set T) (hA : A ⊆ (SectionEvaluation.Constructions.analyticOpen X D.domain : Set T))
    (f : T ⟶ PrincipalBoundary.Constructions.normalComplexLine) (hf : Set.MapsTo f A PrincipalBoundary.Constructions.puncturedComplexLine)
    (hfg : ∀ x : A, f x.val 0 = SectionEvaluation.Constructions.sectionEvaluationOn X D.domain
      (D.unit : Γ(X.left, D.domain)) ⟨x.val, hA x.property⟩) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf 2
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 T) hA 2
      (SupportedPrincipalDivisor.Constructions.principalDivisorSupportedClass X D.domain g) := by
  have h := WindingNormalization.Constructions.BoundaryNaturality.equation_eq_boundary_restriction A (SectionEvaluation.Constructions.analyticOpen X D.domain) hA f hf
    (RationalBoundary.Constructions.Restriction.globalUnitMap X D) hfg
  change _ = AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 T) hA 2
    (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D) at h
  rw [PrincipalDivisorComparison.Constructions.rationalGlobalBoundary_eq_principalDivisorSupportedClass X D hg] at h
  exact h

theorem pullback_equation_eq_principalDivisorSupportedClass
    {Y : TopCat.{0}} (B : Set Y) (i : T ⟶ Y)
    (hA : i ⁻¹' B ⊆ (SectionEvaluation.Constructions.analyticOpen X D.domain : Set T))
    (f : Y ⟶ PrincipalBoundary.Constructions.normalComplexLine) (hf : Set.MapsTo f B PrincipalBoundary.Constructions.puncturedComplexLine)
    (hfg : ∀ x : i ⁻¹' B, f (i x.val) 0 = SectionEvaluation.Constructions.sectionEvaluationOn X D.domain
      (D.unit : Γ(X.left, D.domain)) ⟨x.val, hA x.property⟩) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) i
      (A := i ⁻¹' B) (B := B) (fun _ hx => hx) 2
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf 2
        (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 T) hA 2
      (SupportedPrincipalDivisor.Constructions.principalDivisorSupportedClass X D.domain g) := by
  exact (ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) i f
      (A := i ⁻¹' B) (B := B) (C := PrincipalBoundary.Constructions.puncturedComplexLine) (fun _ hx => hx) hf 2)
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)).trans
      (equation_eq_principalDivisorSupportedClass X D hg (i ⁻¹' B) hA (i ≫ f)
        (fun _ hx => hf hx) hfg)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.EquationDivisor.Constructions
