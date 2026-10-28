import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OrdinaryPolynomial
import OAI.AlgebraicGeometry.HodgeConjecture.GeometricThetaComparisonLevel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.DatumIdentities
import OAI.AlgebraicGeometry.HodgeConjecture.IntrinsicGeometricThetaComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PrincipalGeometricTheta
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicPolynomialExtraction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BettiNonzero
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonIntrinsicClass
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CanonicalActiveEquiv
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CanonicalTest

/-! # Intrinsic Level Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.IntrinsicLevelComparison.CMExtractionIntrinsic

noncomputable section

/-! The full fixed-coordinate projector comparison and Frobenius-purity
output is inhabited by the normalized test chosen before the auxiliary prime,
on the original principal level. -/

open scoped Classical _root_.Matrix TensorProduct
open _root_.CategoryTheory

open OAI.RepresentationTheory.Hecke.RadialDilation.Cm OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CanonicalActiveEquiv.Local

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic
attribute [local instance] NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

theorem native_level_comparison
    (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput)
    (hRadialDilation : RepresentationTheory.Hecke.SphericalAction.RadialDilationInput.{0, 0})
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition) (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    (hRationalStructure : RepresentationTheory.Hecke.GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (hdegree : Module.finrank ℚ E = 2 * s)
    {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (hTateComparison : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D.pel hg hq hIsogenyQuotient)
    (hμ : D.pel.reference.μ = E.val.toRingHom)
    (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (v : CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * CMExtraction.Intrinsic.Multiplicity.nativeTensorPairing E D.pel.reference v x y))
    {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n)
    (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (side : Fin s → Bool)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q)
    (hcomplex : j.complexClosure = RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
    (hopposite : j.iota = CMExtraction.Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D.pel)
    (hpoly : CMExtraction.Intrinsic.OrdinaryPolynomial.NativeOrdinaryPolynomial D.pel hg hq hIsogenyQuotient side j)
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparison.FrobeniusSlope.GeometricComparisonInput) (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (u : MpF)
    (hproject : D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
      (CMExtraction.Intrinsic.FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he))
    (hu : CMExtraction.Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D e u)
    [TopologicalSpace (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)]
    (L : OpenSubgroup (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu))
    (hGeometricTheta : CMExtraction.GeometricTheta.Intrinsic.GeometricThetaOutput (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L) hg hq hIsogenyQuotient)
    (fstar : (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).sphericalInputs)
    (z : (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).domain) (dz : Fin 2 → ℂ)
    (hvalue : (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).thetaUniversal fstar.val z.val dz ≠ 0) :
    IntrinsicGeometricThetaComparison.CMExtractionIntrinsic.NativeGeometricThetaComparisonConclusion E (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L)
      hg v hHodgeDecomposition ιE fstar := by
  exact GeometricThetaComparisonLevel.CMExtractionIntrinsic.nativeGeometricThetaComparisonAtLevel E D hg hμ v hv e he c u hu L hHodgeDecomposition
    hRadialDilation hLocalWeil hPoissonAutomorphy hRationalStructure ιE hq hIsogenyQuotient hElementaryDivisors hproject hdegree hTateComparison hGeometricTheta
    side j hcomplex hopposite hpoly hGeometricComparison ℓ hℓq hConstruction hHodgeComparison fstar z dz hvalue

end

end OAI.AlgebraicGeometry.HodgeConjecture.IntrinsicLevelComparison.CMExtractionIntrinsic
