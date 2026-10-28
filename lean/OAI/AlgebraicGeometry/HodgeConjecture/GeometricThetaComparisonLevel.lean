import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LevelProjection
import OAI.AlgebraicGeometry.HodgeConjecture.IntrinsicGeometricThetaComparison
import OAI.RepresentationTheory.Hecke.IntrinsicDatum
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteCoordinates

/-! # Geometric Theta Comparison Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.GeometricThetaComparisonLevel.CMExtractionIntrinsic

noncomputable section

/-! Literal identities for the constructed native datum, kept separate
so subsequent geometric assembly reuses their checked proofs. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (v : CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * CMExtraction.Intrinsic.Multiplicity.nativeTensorPairing E D.pel.reference v x y))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
  (hu : CMExtraction.Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D e u)

variable [TopologicalSpace (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)]
  (L : OpenSubgroup (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu))

local notation "N" => OAI.RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L

variable
  (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput)
  (hRadialDilation : RepresentationTheory.Hecke.SphericalAction.RadialDilationInput.{0, 0})
  (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition) (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
  (hRationalStructure : RepresentationTheory.Hecke.GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
  (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar)
  (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
  (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
  (hproject : D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
    (CMExtraction.Intrinsic.FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he))
  (hdegree : Module.finrank ℚ E = 2 * s)
  (hTateComparison : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D.pel hg hq hIsogenyQuotient)
  (hGeometricTheta : CMExtraction.GeometricTheta.Intrinsic.GeometricThetaOutput (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L) hg hq hIsogenyQuotient)

include hRadialDilation hLocalWeil hPoissonAutomorphy hRationalStructure hElementaryDivisors hproject hdegree hTateComparison hGeometricTheta in
theorem nativeGeometricThetaComparisonAtLevel : type_of% (IntrinsicGeometricThetaComparison.CMExtractionIntrinsic.nativeGeometricThetaComparisonAtDatum E D hg hμ v hv e he c u hu L hHodgeDecomposition
    hRadialDilation hLocalWeil hPoissonAutomorphy hRationalStructure ιE u hq hIsogenyQuotient c
    (CMExtraction.Intrinsic.LevelProjection.nativeDatum_local_projection E D hg hμ v hv e he c u hu L)
    (fun g _ p t => RepresentationTheory.Hecke.AwayPhase.SphericalActionIntrinsic.nativeDatum_away_fixes_phase E D hg hμ v hv e he c u hu L g p t)
    hElementaryDivisors (CMExtraction.Intrinsic.LevelProjection.nativeDatum_fixed_projection E D hg hμ v hv e he c u hu L hq hproject)
    hdegree hTateComparison hGeometricTheta (CMExtraction.Intrinsic.DatumIdentities.nativeDatum_cotangent_identity E D hg hμ v hv e he c u hu L)) :=
  IntrinsicGeometricThetaComparison.CMExtractionIntrinsic.nativeGeometricThetaComparisonAtDatum E D hg hμ v hv e he c u hu L hHodgeDecomposition
    hRadialDilation hLocalWeil hPoissonAutomorphy hRationalStructure ιE u hq hIsogenyQuotient c
    (CMExtraction.Intrinsic.LevelProjection.nativeDatum_local_projection E D hg hμ v hv e he c u hu L)
    (fun g _ p t => RepresentationTheory.Hecke.AwayPhase.SphericalActionIntrinsic.nativeDatum_away_fixes_phase E D hg hμ v hv e he c u hu L g p t)
    hElementaryDivisors (CMExtraction.Intrinsic.LevelProjection.nativeDatum_fixed_projection E D hg hμ v hv e he c u hu L hq hproject)
    hdegree hTateComparison hGeometricTheta (CMExtraction.Intrinsic.DatumIdentities.nativeDatum_cotangent_identity E D hg hμ v hv e he c u hu L)

end

end OAI.AlgebraicGeometry.HodgeConjecture.GeometricThetaComparisonLevel.CMExtractionIntrinsic
