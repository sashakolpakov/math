import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Naturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ExponentialEdgesIs
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LoopEvaluationEq
import OAI.AlgebraicGeometry.AbelianVariety.InvariantClosed

/-! # Complex Periods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ComplexPeriods.IntrinsicComplexPeriods

noncomputable section

/-!
# ReferenceFamily: actual abelian Betti periods of invariant forms

The constructed topological period comparison agrees with the project's
integration-normalized de Rham comparison. Invariant one-forms have exactly
their identity covector's values on the actual exponential lattice.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LoopEvaluationEq.Constructions.LoopEvaluation
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodEquiv.SingularPeriodComparison OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodEdgesTo.PeriodEdges OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ExponentialEdgesIs.ExponentialEdges

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.IsIntegral A.toOver.left :=
  A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.Smooth A.toOver.hom :=
  A.variety.presentation.smooth

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    LieGroup (𝓘(ℝ, A.variety.analyticModel)) ∞ A.variety.analyticSpace :=
  HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.IntrinsicAbelianLieGroup.realLieGroup A

/-- Canonical complex Betti periods on the actual native period lattice. -/
def complexPeriods (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    A.variety.complexCohomology 1 ≃ₗ[ℂ] (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A →+ ℂ) :=
  (AlgebraicTopology.Cohomology.Singular.Homotopy.singularCohomologyIsoOfHomotopyEquiv (ModuleCat.of ℂ ℂ)
      (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Torsion.IntrinsicTorsion.e06Input A).toHomotopyEquiv 1).toLinearEquiv.trans
    (SingularPeriodEquiv.SingularPeriodComparison.cohomologyPeriodEquiv (K := ℂ) (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A))

/-- A representing cocycle computes its periods on the actual exponential loops. -/
theorem complexPeriods_class (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℂ ℂ) (TopCat.of A.variety.analyticSpace) 1)
    (ℓ : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    complexPeriods A (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℂ ℂ)
      (TopCat.of A.variety.analyticSpace) 1 c) ℓ =
        AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj (TopCat.of A.variety.analyticSpace))
          (ModuleCat.of ℂ ℂ) (ExponentialEdgesIs.ExponentialEdges.smoothExponentialEdge (C := A.variety.analyticSpace) (ℓ : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)).val
          c.val := by
  let q : HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ⟶ TopCat.of A.variety.analyticSpace :=
    TopCat.ofHom ⟨HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Torsion.IntrinsicTorsion.e06Input A, (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Torsion.IntrinsicTorsion.e06Input A).continuous⟩
  change HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) q 1
      (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℂ ℂ) (TopCat.of A.variety.analyticSpace) 1 c)) ℓ = _
  erw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod_class]
  rw [PeriodEdgesTo.PeriodEdges.periodHom_eq_edge_evaluation (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) _ ℓ (PeriodEdgesTo.PeriodEdges.vectorEdge (ℓ : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A))
    (PeriodEdgesTo.PeriodEdges.vectorEdge_zero _) (PeriodEdgesTo.PeriodEdges.vectorEdge_one _)]
  change AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation _ (ModuleCat.of ℂ ℂ) _
      ((AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) (TopCat.toSSet.map q)).f 1 c.val) = _
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.evaluation_pullback_apply]
  apply congrArg (fun s => AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation _ (ModuleCat.of ℂ ℂ) s c.val)
  apply (TopCat.toSSetObjEquiv _ _).injective
  apply ContinuousMap.ext
  intro x
  change HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Torsion.IntrinsicTorsion.e06Input A
      (QuotientAddGroup.mk ((TopCat.of (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)).toSSetObjEquiv _
        (PeriodEdgesTo.PeriodEdges.vectorEdge (ℓ : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) x)) =
    HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := A.variety.analyticSpace)
      ((TopCat.of (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)).toSSetObjEquiv _ (PeriodEdgesTo.PeriodEdges.vectorEdge (ℓ : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) x)
  let : ConnectedSpace A.variety.analyticSpace := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.native_connectedSpace Torsion.IntrinsicTorsion.e06Input A
  exact HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expQuotientHomeomorph_mk _

/-- The genuine invariant form is closed because the group is commutative. -/
def invariantClosedForm (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (α : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A [⋀^Fin 1]→L[ℝ] ℂ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms A.variety.analyticModel A.variety.analyticSpace 1 :=
  ⟨AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantSmoothForm (G := A.variety.analyticSpace) α,
    AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms_closed _ (AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantSmoothForm_mem α)⟩

/-- The actual Betti class of an invariant form has the expected periods. -/
theorem complexPeriods_invariantForm (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (α : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A [⋀^Fin 1]→L[ℝ] ℂ) (ℓ : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    complexPeriods A
      ((A.variety.deRhamBettiIso 1).hom (A.variety.deRhamClass 1 (invariantClosedForm A α))) ℓ =
        α (fun _ => (ℓ : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) := by
  obtain ⟨c, hc⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℂ ℂ)
    (TopCat.of A.variety.analyticSpace) 1
      ((A.variety.deRhamBettiIso 1).hom (A.variety.deRhamClass 1 (invariantClosedForm A α)))
  rw [← hc, complexPeriods_class]
  erw [HodgeConjecture.DegreeTwo.LoopEvaluationEq.Constructions.LoopEvaluation.betti_form_evaluation A.variety (invariantClosedForm A α) c hc
    (ExponentialEdgesIs.ExponentialEdges.smoothExponentialEdge (C := A.variety.analyticSpace) (ℓ : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A))
    (ExponentialEdgesIs.ExponentialEdges.smoothExponentialEdge_isLoop ℓ)]
  exact ExponentialEdgesIs.ExponentialEdges.smoothExponentialEdge_integration α (ℓ : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)

theorem complexPeriods_rationalToComplex (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (u : A.variety.rationalCohomology 1) (ℓ : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    complexPeriods A
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (TopCat.of A.variety.analyticSpace) 1 u) ℓ =
        (HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A u
          (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ) : ℂ) := by
  let q : HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ⟶ TopCat.of A.variety.analyticSpace :=
    TopCat.ofHom ⟨HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Torsion.IntrinsicTorsion.e06Input A, (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Torsion.IntrinsicTorsion.e06Input A).continuous⟩
  have hn := ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology_naturality q 1) u
  change AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)) 1
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) q 1 u) =
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) q 1
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (TopCat.of A.variety.analyticSpace) 1 u) at hn
  change HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod (K := ℂ) (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) q 1
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (TopCat.of A.variety.analyticSpace) 1 u)) ℓ = _
  rw [← hn, PeriodEdgesTo.PeriodEdges.cohomologyPeriod_rationalToComplex]
  apply congrArg (fun r : ℚ => (r : ℂ))
  exact (Naturality.IntrinsicRationalPeriods.nativeH1Periods_lattice A u ℓ).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ComplexPeriods.IntrinsicComplexPeriods
