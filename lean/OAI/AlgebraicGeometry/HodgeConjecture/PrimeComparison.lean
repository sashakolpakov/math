import OAI.AlgebraicGeometry.HodgeConjecture.PrimeComparisonConclusion
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinarySetup
import OAI.AlgebraicGeometry.HodgeConjecture.ModelComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Theta
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Lattices

/-! # Prime Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.PrimeComparison.CMExtractionIntrinsic

noncomputable section

/-! Choose one good split prime for the fixed model and normalized test,
then extract the CM classes from its full geometric correspondences. -/

open scoped Classical _root_.Matrix
open _root_.CategoryTheory
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)
  (R : CMExtraction.PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W)
  (M : CMExtraction.Moduli.Intrinsic.RetainedModuli E P hP hμ v hv W R)

theorem exists_retained_prime_comparison
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hzero : P.distinguished.val = 0)
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
    (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (excluded : Finset ℕ) (bound : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime),
      let : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧ PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt E q ∧
      PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt M.integral.base.extension.carrier q ∧
      PrimeComparisonConclusion.CMExtractionIntrinsic.RetainedPrimeComparisonConclusion E P hP hμ v hv W R M ιE q := by
  obtain ⟨q, hq, hb, hx, hE, hK, hgood, j₀, hchoices⟩ :=
    CMExtraction.OrdinarySetup.Intrinsic.exists_retained_ordinary_setup hOpenness hSplitPrimes hHilb hEnd hCMAbelianVarietyA hCMAbelianVarietyM E hs hdegree
      P hP hμ v hv W R M ιE excluded bound
  let : Fact q.Prime := ⟨hq⟩
  refine ⟨q, hq, hb, hx, hE, hK, hgood, j₀, ?_⟩
  intro C hIsogenyQuotient
  obtain ⟨j, hc, hop, hj, hsplit, T, hgeom⟩ := hchoices C
  exact ModelComparison.CMExtractionIntrinsic.retained_model_comparison E P hP hμ v hv W R M j₀ C hs hdegree hzero hgood hIsogenyQuotient
    ιE j hc hop hj hsplit T hgeom CMExtraction.Theta.verifiedHodgeDecomposition hGeometricTheta hRadialDilation hLocalWeil hPoissonAutomorphy hRationalStructure
    hTateComparison hConstruction hHodgeComparison (CMExtraction.Lattices.Intrinsic.verifiedElementaryDivisors ℤ_[q] ℚ_[q]) hNeighborCounting hFrobeniusKernel hCMPoints hCartierDuality hTorsionQuotient hGeometricComparison

end

end OAI.AlgebraicGeometry.HodgeConjecture.PrimeComparison.CMExtractionIntrinsic
