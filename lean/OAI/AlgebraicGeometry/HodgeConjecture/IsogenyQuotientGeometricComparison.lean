import OAI.AlgebraicGeometry.HodgeConjecture.PrimeComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InitialCofinalModuli
import OAI.AlgebraicGeometry.HodgeConjecture.GeometricConclusion

/-! # Isogeny Quotient Geometric Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.IsogenyQuotientGeometricComparison.CMExtractionIntrinsic

noncomputable section

/-! Geometric isogeny-quotient comparison at every sufficiently divisible source level. The
source reference and normalized test precede all level and prime choices.
Only the identified complete upstream propositions remain inputs. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

theorem geometric_comparison_from_full_IsogenyQuotient
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (B : HeckeCycles.GeometricSource.CM.BallDatum E) (places : HeckeCycles.GeometricSource.CM.Places E) (hCongruenceLevel : HeckeCycles.ReferenceDatum.CM.CongruenceLevelInput E places.count)
    (hAdelicTheta : RepresentationTheory.Theta.Adelic.Data.CompleteStatement)
    (hReferenceFamily : AbelianScheme.IsogenyQuotient.Reference.Family.Construction.ReferenceFamilyInput) (hIntegralModel : RepresentationTheory.Hecke.IntegralModel.OrdinaryCharacterIntrinsic.FullIntegralModelInput)
    (hIsogenyQuotient : CMExtraction.IsogenyQuotient.Transport.CompleteIsogenyQuotientTransportInput) (hFiniteDescent : AbelianScheme.IsogenyQuotient.IsogenyComplement.Construction.FiniteDescentInput.{0})
    (hOpenness : PELModuli.CMPoints.OrdinaryReduction.OpennessInput) (hSplitPrimes : PELModuli.CMPoints.Arithmetic.SplitPrimesInput)
    (hHilb : PELModuli.IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) (hEnd : PELModuli.IntegralModel.Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hCMAbelianVarietyA : PELModuli.CMPoints.Descent.AbelianInput) (hCMAbelianVarietyM : PELModuli.CMPoints.Descent.ModuliInput)
    (hGeometricTheta : RepresentationTheory.Hecke.SphericalAction.GeometricThetaInput) (hRadialDilation : RepresentationTheory.Hecke.SphericalAction.RadialDilationInput.{0, 0})
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition) (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    (hRationalStructure : RepresentationTheory.Hecke.GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    (hTateComparison : HeckeCycles.TateComparison.CM.TateComparisonInput) (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput)
    (hNeighborCounting : HeckeCycles.Neighbor.Counting.CM.NeighborCountingInput) (hFrobeniusKernel : Isogenies.NeighborCounting.Prerequisites.FullFrobeniusKernelInput)
    (hCMPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{0, 0}) (hCartierDuality : AbelianScheme.FrobeniusKernel.CartierDuality.Construction.FullCartierDualityInput.{0}) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0})
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparison.FrobeniusSlope.GeometricComparisonInput)
    (dref : Fin places.count → Bool) (v : CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
    (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin places.count × Fin 3) MpR MpF MpA)
    (base : ℕ) (hbase : 0 < base) :
    GeometricConclusion.CMExtractionIntrinsic.FullIsogenyQuotientGeometricComparisonConclusion E B places dref v hv W base hFiniteDescent := by
  obtain ⟨P, hP, hμ, hb, hz, he, hd, R, N, hN, hbN, hrN, hlevels⟩ :=
    CMExtraction.InitialCofinalModuli.Intrinsic.exists_initial_cofinal_moduli E B places hCongruenceLevel hAdelicTheta hReferenceFamily hIntegralModel dref v hv W base hbase
  refine ⟨P, hP, hμ, hb, hz, he, hd, R, N, hN, hbN, hrN, ?_⟩
  intro L hL hNL
  obtain ⟨M, hM⟩ := hlevels L hL hNL
  refine ⟨M, hM, ?_⟩
  intro excluded bound
  obtain ⟨q, hq, hbound, hexcluded, hsplitE, hsplitK, hconditional⟩ :=
    PrimeComparison.CMExtractionIntrinsic.exists_retained_prime_comparison E P hP hμ v hv W R M
      (HeckeCycles.ReferenceDatum.CM.source_degree E places).1 (HeckeCycles.ReferenceDatum.CM.source_degree E places).2 hz hOpenness hSplitPrimes hHilb hEnd hCMAbelianVarietyA hCMAbelianVarietyM
      hGeometricTheta hRadialDilation hLocalWeil hPoissonAutomorphy hRationalStructure hTateComparison hConstruction hHodgeComparison hNeighborCounting hFrobeniusKernel hCMPoints hCartierDuality hTorsionQuotient hGeometricComparison
      (CMExtraction.ParameterChoices.algebraicEmbedding E) excluded bound
  let : Fact q.Prime := ⟨hq⟩
  exact ⟨q, hq, hbound, hexcluded, hsplitE, hsplitK,
    IsogenyQuotientComparison.CMExtractionIntrinsic.fullIsogenyQuotient_retained_comparison E P hP hμ v hv W R M
      (HeckeCycles.ReferenceDatum.CM.source_degree E places).1 (HeckeCycles.ReferenceDatum.CM.source_degree E places).2 hFiniteDescent q (CMExtraction.ParameterChoices.algebraicEmbedding E)
      hIsogenyQuotient hconditional⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.IsogenyQuotientGeometricComparison.CMExtractionIntrinsic
