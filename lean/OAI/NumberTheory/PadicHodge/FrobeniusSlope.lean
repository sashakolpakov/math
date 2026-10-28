import OAI.AlgebraicGeometry.HodgeConjecture.ComparisonEstablished
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ProjectiveModelsAlbanese
import OAI.NumberTheory.PadicHodge.GeometricComparison.Public

/-! # Frobenius Slope -/

namespace OAI.NumberTheory.PadicHodge.FrobeniusSlope

noncomputable section

/-! FrobeniusSlope on the actual retained geometric model, with every full theorem
input supplied by the existing unconditional ReferenceFamily, IntegralModel and GeometricComparison proofs. -/
open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.ComparisonEstablished.CMExtractionIntrinsic
attribute [local instance] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

theorem full_comparison_input : GeometricComparison.FrobeniusSlope.GeometricComparisonInput := by
  exact GeometricComparison.Public.comparison_and_weak_admissibility_on_hecke_summands

theorem retained_comparison_unconditional
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (B : AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM.BallDatum E) (places : AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM.Places E)
    (dref : Fin places.count → Bool) (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
    (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin places.count × Fin 3) MpR MpF MpA)
    (base : ℕ) (hbase : 0 < base) :
    AlgebraicGeometry.HodgeConjecture.GeometricConclusion.CMExtractionIntrinsic.FullIsogenyQuotientGeometricComparisonConclusion E B places dref v hv W base
      AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.Descent.Construction.verifiedFiniteDescentInput := by
  have h43 : AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.Family.Construction.ReferenceFamilyInput := AlgebraicGeometry.PELModuli.IntegralModel.ReferenceFamilyConstructed.provedReferenceFamilyModuliInput
  have h44 : RepresentationTheory.Hecke.IntegralModel.OrdinaryCharacterIntrinsic.FullIntegralModelInput :=
    AlgebraicGeometry.PELModuli.IntegralModel.ProjectiveModelsAlbanese.projective_models_and_albanese_generation_unconditional
  exact AlgebraicGeometry.HodgeConjecture.ComparisonEstablished.CMExtractionIntrinsic.geometric_comparison_from_constructed_inputs E B places h43 h44
    full_comparison_input dref v hv W base hbase

end

end OAI.NumberTheory.PadicHodge.FrobeniusSlope
