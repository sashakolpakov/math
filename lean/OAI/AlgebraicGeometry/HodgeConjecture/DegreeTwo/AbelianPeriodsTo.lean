import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialEdges
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LoopEvaluationEq
import OAI.AlgebraicGeometry.AbelianVariety.InvariantClosed

/-! # Abelian Periods To -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianPeriodsTo.Constructions.AbelianPeriods

noncomputable section

/-!
# DegreeTwo: actual abelian Betti periods of invariant forms

The constructed topological period comparison agrees with the project's
integration-normalized de Rham comparison. Invariant one-forms have exactly
their identity covector's values on the actual exponential lattice.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialEdges.Constructions.Exponential
  PeriodSurjectivityOne.Constructions.PeriodSurjectivity LoopEvaluationEq.Constructions.LoopEvaluation

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.IsIntegral A.toOver.left :=
  A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.Smooth A.toOver.hom :=
  A.variety.presentation.smooth

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    LieGroup (𝓘(ℝ, A.variety.analyticModel)) ∞ A.variety.analyticSpace :=
  IntrinsicProductMaps.Constructions.IntrinsicAbelianLieGroup.realLieGroup A

/-- Canonical complex Betti periods on the actual native period lattice. -/
def complexPeriods (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    A.variety.complexCohomology 1 ≃ₗ[ℂ] (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A →+ ℂ) :=
  (AlgebraicTopology.Cohomology.Singular.Homotopy.singularCohomologyIsoOfHomotopyEquiv (ModuleCat.of ℂ ℂ)
      (AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph hHolomorphicAlgebraicity A).toHomotopyEquiv 1).toLinearEquiv.trans
    (PeriodSurjectivityOne.Constructions.PeriodSurjectivity.cohomologyPeriodEquiv (K := ℂ) (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A))

/-- A representing cocycle computes its periods on the actual exponential loops. -/
theorem complexPeriods_class (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℂ ℂ) (TopCat.of A.variety.analyticSpace) 1)
    (ℓ : AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    complexPeriods hHolomorphicAlgebraicity A (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℂ ℂ)
      (TopCat.of A.variety.analyticSpace) 1 c) ℓ =
        AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj (TopCat.of A.variety.analyticSpace))
          (ModuleCat.of ℂ ℂ) (ExponentialEdges.Constructions.Exponential.smoothExponentialEdge (C := A.variety.analyticSpace) (ℓ : Transport.Constructions.AbelianModel A)).val
          c.val := by
  let q : SingularPeriodsD.Constructions.SingularPeriods.Base (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ⟶ TopCat.of A.variety.analyticSpace :=
    TopCat.ofHom ⟨AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph hHolomorphicAlgebraicity A, (AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph hHolomorphicAlgebraicity A).continuous⟩
  change SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) q 1
      (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℂ ℂ) (TopCat.of A.variety.analyticSpace) 1 c)) ℓ = _
  erw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod_class]
  rw [PeriodEdges.Constructions.SingularPeriods.periodHom_eq_edge_evaluation (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) _ ℓ (PeriodEdges.Constructions.SingularPeriods.vectorEdge (ℓ : Transport.Constructions.AbelianModel A))
    (PeriodEdges.Constructions.SingularPeriods.vectorEdge_zero _) (PeriodEdges.Constructions.SingularPeriods.vectorEdge_one _)]
  change AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation _ (ModuleCat.of ℂ ℂ) _
      ((AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) (TopCat.toSSet.map q)).f 1 c.val) = _
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.evaluation_pullback_apply]
  apply congrArg (fun s => AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation _ (ModuleCat.of ℂ ℂ) s c.val)
  apply (TopCat.toSSetObjEquiv _ _).injective
  apply ContinuousMap.ext
  intro x
  change AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph hHolomorphicAlgebraicity A
      (QuotientAddGroup.mk ((TopCat.of (Transport.Constructions.AbelianModel A)).toSSetObjEquiv _
        (PeriodEdges.Constructions.SingularPeriods.vectorEdge (ℓ : Transport.Constructions.AbelianModel A)) x)) =
    ExponentialM.Constructions.Exponential.expMap (C := A.variety.analyticSpace)
      ((TopCat.of (Transport.Constructions.AbelianModel A)).toSSetObjEquiv _ (PeriodEdges.Constructions.SingularPeriods.vectorEdge (ℓ : Transport.Constructions.AbelianModel A)) x)
  let : ConnectedSpace A.variety.analyticSpace := AbelianUniformizationEq.Constructions.AbelianUniformization.native_connectedSpace hHolomorphicAlgebraicity A
  exact ExponentialLocal.Constructions.Exponential.expQuotientHomeomorph_mk _

/-- The genuine invariant form is closed because the group is commutative. -/
def invariantClosedForm (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (α : Transport.Constructions.AbelianModel A [⋀^Fin 1]→L[ℝ] ℂ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms A.variety.analyticModel A.variety.analyticSpace 1 :=
  ⟨AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantSmoothForm (G := A.variety.analyticSpace) α,
    AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms_closed _ (AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantSmoothForm_mem α)⟩

/-- The actual Betti class of an invariant form has the expected periods. -/
theorem complexPeriods_invariantForm (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (α : Transport.Constructions.AbelianModel A [⋀^Fin 1]→L[ℝ] ℂ) (ℓ : AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    complexPeriods hHolomorphicAlgebraicity A
      ((A.variety.deRhamBettiIso 1).hom (A.variety.deRhamClass 1 (invariantClosedForm A α))) ℓ =
        α (fun _ => (ℓ : Transport.Constructions.AbelianModel A)) := by
  obtain ⟨c, hc⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℂ ℂ)
    (TopCat.of A.variety.analyticSpace) 1
      ((A.variety.deRhamBettiIso 1).hom (A.variety.deRhamClass 1 (invariantClosedForm A α)))
  rw [← hc, complexPeriods_class]
  erw [LoopEvaluationEq.Constructions.LoopEvaluation.betti_form_evaluation A.variety (invariantClosedForm A α) c hc
    (ExponentialEdges.Constructions.Exponential.smoothExponentialEdge (C := A.variety.analyticSpace) (ℓ : Transport.Constructions.AbelianModel A))
    (ExponentialEdges.Constructions.Exponential.smoothExponentialEdge_isLoop ℓ)]
  exact ExponentialEdges.Constructions.Exponential.smoothExponentialEdge_integration α (ℓ : Transport.Constructions.AbelianModel A)

theorem complexPeriods_rationalToComplex (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (u : A.variety.rationalCohomology 1) (ℓ : AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    complexPeriods hHolomorphicAlgebraicity A
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (TopCat.of A.variety.analyticSpace) 1 u) ℓ =
        (AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity A u
          (LatticePeriod.Constructions.LatticeDual.latticeInclusion (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ) : ℂ) := by
  let q : SingularPeriodsD.Constructions.SingularPeriods.Base (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ⟶ TopCat.of A.variety.analyticSpace :=
    TopCat.ofHom ⟨AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph hHolomorphicAlgebraicity A, (AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph hHolomorphicAlgebraicity A).continuous⟩
  have hn := ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology_naturality q 1) u
  change AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (SingularPeriodsD.Constructions.SingularPeriods.Base (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)) 1
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) q 1 u) =
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) q 1
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (TopCat.of A.variety.analyticSpace) 1 u) at hn
  change SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod (K := ℂ) (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) q 1
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (TopCat.of A.variety.analyticSpace) 1 u)) ℓ = _
  rw [← hn, PeriodEdges.Constructions.SingularPeriods.cohomologyPeriod_rationalToComplex]
  apply congrArg (fun r : ℚ => (r : ℂ))
  have he := (LatticePeriod.Constructions.LatticeDual.characterRestrictionEquiv (K := ℚ) (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)).apply_symm_apply
    (SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) q 1 u))
  exact (DFunLike.congr_fun he ℓ).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianPeriodsTo.Constructions.AbelianPeriods
