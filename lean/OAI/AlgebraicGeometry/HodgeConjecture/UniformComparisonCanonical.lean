import OAI.AlgebraicGeometry.HodgeConjecture.UniformComparison
import OAI.RepresentationTheory.Hecke.GaloisValuationFrom
import OAI.RepresentationTheory.Hecke.EstablishedAction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MarkedLevel
import OAI.RepresentationTheory.Satake.RationalStructure

/-! # Uniform Comparison Canonical -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.UniformComparisonCanonical.CMExtractionIntrinsic

noncomputable section

/-! Construct the marked level and full geometric theta output once. The
result keeps the original radial parameters uniform over all characters,
on the same integral model and compatible comparison place. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (v : CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)

def UniformComparisonOnData
    (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (side : Fin s → Bool) (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q) : Prop :=
  ∃ (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * CMExtraction.Intrinsic.Multiplicity.nativeTensorPairing E D.pel.reference v x y))
    (u : MpF) (hu : CMExtraction.Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D e u),
    let := CMExtraction.Intrinsic.UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he (Fintype.equivFin _) u hu
      (CMExtraction.Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D)
    let := CMExtraction.Intrinsic.UnitaryAwayTopology.nativeUnitaryAway_topologicalGroup E D hg hμ v hv e he (Fintype.equivFin _) u hu
      (CMExtraction.Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D)
    ∃ hN : 0 < D.pel.level,
      UniformComparison.CMExtractionIntrinsic.UniformFullOutput E (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he (Fintype.equivFin _) u hu
        (CMExtraction.Intrinsic.PELLevel.nativePELLevel E D hg hμ v hv e he (Fintype.equivFin _) u hu
          (CMExtraction.Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D) hN)) u ιE v hg hq hIsogenyQuotient side j

theorem uniform_comparison_on_constructed_data
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (hc : D.HasFiniteCoordinates) (side : Fin s → Bool)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q)
    (hcomplex : j.complexClosure = RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
    (hopposite : j.iota = CMExtraction.Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D.pel)
    (hpoly : CMExtraction.Intrinsic.OrdinaryPolynomial.NativeOrdinaryPolynomial D.pel hg hq hIsogenyQuotient side j)
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparison.FrobeniusSlope.GeometricComparisonInput) :
    UniformComparisonOnData E D hg hμ ιE v hv hq hIsogenyQuotient side j := by
  let c := Fintype.equivFin (Fin s × Fin 3)
  obtain ⟨e, he, u, hu, H⟩ := RepresentationTheory.Hecke.GaloisValuationFrom.native_galois_valuations_from_geometric_inputs
    E hs hdegree D hg hq hIsogenyQuotient hc hμ ιE v hv c
  refine ⟨e, he, u, hu, ?_⟩
  let := CMExtraction.Intrinsic.UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu (CMExtraction.Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D)
  let := CMExtraction.Intrinsic.UnitaryAwayTopology.nativeUnitaryAway_topologicalGroup E D hg hμ v hv e he c u hu (CMExtraction.Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D)
  have hN : 0 < D.pel.level := Nat.lt_of_lt_of_le (by decide : 0 < 3) hg.fullLevel
  refine ⟨hN, ?_⟩
  let L := CMExtraction.Intrinsic.PELLevel.nativePELLevel E D hg hμ v hv e he c u hu (CMExtraction.Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D) hN
  have hL := CMExtraction.Intrinsic.MarkedLevel.nativePELLevel_marked E D hg hμ v hv e he c u hu hN hq hc.1 hc.2.1
  have hdense := CMExtraction.Intrinsic.UnitaryAwayDensity.native_unitary_away_density E D hg hμ v hv e he c u hu L
  have hTateComparison := RepresentationTheory.Hecke.EstablishedAction.CentralConstraintIntrinsic.proved_action_output D.pel hg hq hIsogenyQuotient hdegree hs
  exact UniformComparison.CMExtractionIntrinsic.uniformFullOutput_of_geometric E (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L)
    u ιE v hg hq hIsogenyQuotient side j hdegree hTateComparison hμ hv
    RepresentationTheory.Satake.RationalStructure.Construction.normalized_satake_rational_structure hcomplex hopposite hpoly hGeometricComparison (H L hL hdense)

def UniformComparisonModelConclusion : Prop :=
  ∃ (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (side : Fin s → Bool) (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q),
    j.complexClosure = RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE ∧
    j.iota = CMExtraction.Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D.pel ∧
    UniformComparisonOnData E D hg hμ ιE v hv hq hIsogenyQuotient side j

end

end OAI.AlgebraicGeometry.HodgeConjecture.UniformComparisonCanonical.CMExtractionIntrinsic
