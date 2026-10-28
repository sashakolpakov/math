import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FixedGeometric
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MarkedLevel

/-! # Principal Geometric Theta -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PrincipalGeometricTheta

noncomputable section

/-! The full geometric construction on the actual principal native
away level, with its marked meaning and density proved internally. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

theorem native_principal_c48_output
    (hGeometricTheta : RepresentationTheory.Hecke.SphericalAction.GeometricThetaInput)
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (hTateComparison : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D.pel hg hq hIsogenyQuotient)
    (hc : D.HasFiniteCoordinates)
    (hμ : D.pel.reference.μ = E.val.toRingHom)
    (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
      (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
        Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
      (u : MpF) (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)
    (hN : 0 < D.pel.level) :
    let := UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D)
    GeometricTheta.Intrinsic.GeometricThetaOutput
      (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu
        (PELLevel.nativePELLevel E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D) hN))
      hg hq hIsogenyQuotient := by
  let := UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D)
  let := UnitaryAwayTopology.nativeUnitaryAway_topologicalGroup E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D)
  let L := PELLevel.nativePELLevel E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D) hN
  have hL := MarkedLevel.nativePELLevel_marked E D hg hμ v hv e he c u hu hN hq hc.1 hc.2.1
  have hd := UnitaryAwayDensity.native_unitary_away_density E D hg hμ v hv e he c u hu
  dsimp only at hd
  exact hGeometricTheta hs hdegree (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L) hg hq hIsogenyQuotient hTateComparison
    (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum_finiteCoordinates E D hg hμ v hv e he c u hu L hc hL)
    (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum_holomorphic E D hg hμ v hv e he c u hu L)
    (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum_automorphy E D hg hμ v hv e he c u hu L) (hd L)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PrincipalGeometricTheta
