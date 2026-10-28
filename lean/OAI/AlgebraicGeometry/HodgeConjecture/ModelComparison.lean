import OAI.AlgebraicGeometry.HodgeConjecture.ModelComparisonConclusion
import OAI.AlgebraicGeometry.HodgeConjecture.FixedPrincipalComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Polynomial
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeSeed
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparison

/-! # Model Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ModelComparison.CMExtractionIntrinsic

noncomputable section

/-! Extract CM classes on the retained integral model, using its actual
ordinary reduction and the normalized test fixed before the prime. -/

open scoped Classical _root_.Matrix TensorProduct
open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)
  (R : CMExtraction.PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W)
  (M : CMExtraction.Moduli.Intrinsic.RetainedModuli E P hP hμ v hv W R)
  {q : ℕ} [Fact q.Prime]
  (j₀ : PELModuli.CMPoints.Arithmetic.QadicChoice M.integral.base.extension.carrier M.integral.base.embedding q)
  (C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence
    ((Over.pullback M.integral.base.generic).obj M.integral.spread.toOver))

local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j₀ C
local notation "hg" => OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeModel.Intrinsic.retainedHeckeModel_geometry E P hP hμ v hv W R M j₀ C
local notation "Q" => OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryModel.Intrinsic.retainedOrdinaryModel E P hP hμ v hv W R M
local notation "a₀" => OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryHeckeModel.Intrinsic.retainedOrdinaryIndex E P hP hμ v hv W R M

theorem retained_model_comparison
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hzero : P.distinguished.val = 0)
    (hgood : CMExtraction.PrimeBounds.Intrinsic.RetainedPrimeConditions E P hP hμ v hv W R M q)
    (hIsogenyQuotient : (HD).RealizesIsogenyQuotient)
    (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice M.integral.base.extension.carrier M.integral.base.embedding q)
    (hcomplex : j.complexClosure = RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
    (hopposite : j.iota = CMExtraction.Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE HD)
    (hj : (HeckeCycles.QadicModelMap.CM.localFieldEmbedding j).comp (algebraMap E M.integral.base.extension.carrier) =
      CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding HD (P.distinguished, true))
    (hsplit : j.HasSplitCoordinates (Q).extendedEmbedding)
    (T : (Q).GoodIntegralReduction q j) (hgeom : AbelianScheme.FrobeniusKernel.CMPoints.Construction.GeometricConclusion T)
    (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput)
    (hGeometricTheta : RepresentationTheory.Hecke.SphericalAction.GeometricThetaInput) (hRadialDilation : RepresentationTheory.Hecke.SphericalAction.RadialDilationInput.{0, 0})
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition) (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    (hRationalStructure : RepresentationTheory.Hecke.GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    (hTateComparison : HeckeCycles.TateComparison.CM.TateComparisonInput)
    (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (hNeighborCounting : HeckeCycles.Neighbor.Counting.CM.NeighborCountingInput) (hFrobeniusKernel : Isogenies.NeighborCounting.Prerequisites.FullFrobeniusKernelInput)
    (hCMPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{0, 0}) (hCartierDuality : AbelianScheme.FrobeniusKernel.CartierDuality.Construction.FullCartierDualityInput.{0}) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0})
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparison.FrobeniusSlope.GeometricComparisonInput) :
    ModelComparisonConclusion.CMExtractionIntrinsic.RetainedModelComparisonConclusion E P hP hμ v hv W R M j₀ C hHodgeDecomposition ιE := by
  have hqD := CMExtraction.HeckeModel.Intrinsic.retainedHeckeModel_good_prime E P hP hμ v hv W R M j₀ C hgood
  let side := CMExtraction.Intrinsic.Polynomial.retainedOrdinarySide E P hP hμ v hv W R M hs hdegree
  have hpoly : CMExtraction.Intrinsic.OrdinaryPolynomial.NativeOrdinaryPolynomial HD hg hqD hIsogenyQuotient side j := by
    exact CMExtraction.Intrinsic.Polynomial.retained_integral_ordinary_polynomial E P hP hμ v hv W R M j₀ C j hj
      hs hdegree hzero hsplit T hgeom (hgeom.1 a₀).1 (hgeom.1 a₀).2
      hgood.denominator_coprime
      hNeighborCounting hFrobeniusKernel hCMPoints hCartierDuality hTorsionQuotient hg hqD hIsogenyQuotient
  exact ModelComparisonConclusion.CMExtractionIntrinsic.retained_seed_comparison E P hP hμ v hv W R M j₀ C hs hdegree hgood hIsogenyQuotient
    ιE side j hcomplex hopposite hpoly hHodgeDecomposition hGeometricTheta hRadialDilation hLocalWeil hPoissonAutomorphy hRationalStructure hTateComparison hConstruction hHodgeComparison hElementaryDivisors hGeometricComparison

end

end OAI.AlgebraicGeometry.HodgeConjecture.ModelComparison.CMExtractionIntrinsic
