import OAI.AlgebraicGeometry.HodgeConjecture.IsogenyQuotientGeometricComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedAuxiliary
import OAI.RepresentationTheory.Theta.Adelic.UnitaryThetaCongruence
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.TransportFaithfulness
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.Descent
import OAI.RepresentationTheory.Hecke.CMPointsConstruction
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Action
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Construction
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Construction
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.Open
import OAI.NumberTheory.Splitting.SplitPrimes
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.Hom
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EndomorphismEquationLoci
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstructionCapstone
import OAI.AlgebraicGeometry.PELModuli.CMPoints.EstablishedDescent
import OAI.RepresentationTheory.Hecke.EstablishedTheta
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HodgeComparisonCapstone
import OAI.RepresentationTheory.Satake.RationalStructure

/-! # Comparison Established -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ComparisonEstablished.CMExtractionIntrinsic

noncomputable section

/-! Assemble the proved geometric and automorphic prerequisites for the full
extraction conclusion. The reference-family, integral-model, and comparison
inputs remain explicit hypotheses. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

theorem geometric_comparison_from_constructed_inputs
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (B : HeckeCycles.GeometricSource.CM.BallDatum E) (places : HeckeCycles.GeometricSource.CM.Places E)
    (hReferenceFamily : AbelianScheme.IsogenyQuotient.Reference.Family.Construction.ReferenceFamilyInput) (hIntegralModel : RepresentationTheory.Hecke.IntegralModel.OrdinaryCharacterIntrinsic.FullIntegralModelInput)
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparison.FrobeniusSlope.GeometricComparisonInput)
    (dref : Fin places.count → Bool) (v : CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
    (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin places.count × Fin 3) MpR MpF MpA)
    (base : ℕ) (hbase : 0 < base) :
    GeometricConclusion.CMExtractionIntrinsic.FullIsogenyQuotientGeometricComparisonConclusion E B places dref v hv W base
      AbelianScheme.IsogenyQuotient.Finite.Descent.Construction.verifiedFiniteDescentInput := by
  exact IsogenyQuotientGeometricComparison.CMExtractionIntrinsic.geometric_comparison_from_full_IsogenyQuotient E B places
    (HeckeCycles.EstablishedAuxiliary.CM.reference_datum E places.count)
    RepresentationTheory.Theta.Adelic.UnitaryThetaCongruence.complete_unitary_splitting_geometric_theta_and_congruence
    hReferenceFamily hIntegralModel CMExtraction.IsogenyQuotient.TransportFaithfulness.completeIsogenyQuotientTransportInput_of_native
    AbelianScheme.IsogenyQuotient.Finite.Descent.Construction.verifiedFiniteDescentInput
    ArithmeticGeometry.OrdinaryLocus.Openness.Open.Construction.isOpen_ordinaryLocus NumberTheory.Splitting.SplitPrimes.Construction.chebotarev_splitting
    HilbertScheme.Presentations.Relative.Hom.Core.relative_hilbert_and_hom_loci
    HilbertScheme.Presentations.EndomorphismEquationLoci.Core.endomorphism_equation_loci
    PELModuli.CMPoints.EstablishedDescent.abelian_descent PELModuli.CMPoints.EstablishedDescent.moduli_descent
    RepresentationTheory.Hecke.EstablishedTheta.CentralConstraintIntrinsic.proved_theta_covariance_input RepresentationTheory.Hecke.EstablishedTheta.CentralConstraintIntrinsic.proved_dilation_input
    RepresentationTheory.Hecke.EstablishedTheta.CentralConstraintIntrinsic.proved_local_weil_input RepresentationTheory.Hecke.EstablishedTheta.CentralConstraintIntrinsic.proved_poisson_input
    RepresentationTheory.Satake.RationalStructure.Construction.normalized_satake_rational_structure
    AbelianScheme.TateComparison.Action.spherical_hecke_algebra_action_constructed
    PELModuli.IntegralModel.ConstructionCapstone.provedConstructionInput PELModuli.IntegralModel.HodgeComparisonCapstone.provedHodgeComparisonInput
    Isogenies.NeighborCounting.Construction.ordinary_neighbor_reduction_multiplicities
    AbelianScheme.FrobeniusKernel.Construction.ordinary_kernel_operators_and_frobenius
    (RepresentationTheory.Hecke.CMPointsConstruction.OrdinaryCharacterIntrinsic.provedCMPointsInput
      ArithmeticGeometry.OrdinaryLocus.Openness.Open.Construction.isOpen_ordinaryLocus NumberTheory.Splitting.SplitPrimes.Construction.chebotarev_splitting
      HilbertScheme.Presentations.Relative.Hom.Core.relative_hilbert_and_hom_loci
      HilbertScheme.Presentations.EndomorphismEquationLoci.Core.endomorphism_equation_loci)
    AbelianScheme.FrobeniusKernel.CartierDuality.Construction.fullCartierDualityInput_proved AbelianScheme.IsogenyQuotient.Torsion.Construction.verified_TorsionQuotientInput hGeometricComparison
    dref v hv W base hbase

end

end OAI.AlgebraicGeometry.HodgeConjecture.ComparisonEstablished.CMExtractionIntrinsic
