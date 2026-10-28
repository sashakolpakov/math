import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaNamed
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaFiniteCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaHolomorphy
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum

/-! # Theta Realization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaRealization.CM

noncomputable section

/-! Apply the full TateComparison and GeometricTheta named inputs to the actual source
candidate. The one-step IsogenyQuotient realization remains an explicit intermediate
geometric hypothesis; this is not the full IsogenyQuotient prerequisite. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K places.count q) (hb : D.reference.b = B.b)
  (hμ : D.reference.μ = E.val.toRingHom)
  {J : Type*} [Fintype J] [DecidableEq J] [Submodule.IsLattice ℚ D.reference.lattice]
  (b : Module.Basis J ℤ D.reference.lattice) (hN : 0 < D.level)

include hμ in
theorem realization (hTateComparison : TateComparison.CM.TateComparisonInput) (hGeometricTheta : Geometric.Theta.CM.GeometricThetaInput)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)
    (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (hstandard : ∀ v, CMExtraction.SplitLatticeProduct.TestTransport.splitLatticeLocal (R := PadicInt q) (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice v =
      RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.standardLocalLattice (q := q)) :
    Geometric.Theta.CM.Output (ThetaCandidate.CM.data E L D hb b hN) hg hq hIsogenyQuotient :=
  Geometric.ThetaNamed.CM.apply (ThetaCandidate.CM.data E L D hb b hN) hg hq hIsogenyQuotient hTateComparison hGeometricTheta
    (ReferenceDatum.CM.source_degree E places).1 (ReferenceDatum.CM.source_degree E places).2
    hConstruction hElementaryDivisors
    (ThetaFiniteCoordinates.CM.coordinates E L D hb b hN hg hq hstandard)
    (ThetaHolomorphy.CM.holomorphic E L D hb b hN hμ)
    (ThetaHolomorphy.CM.covariance E L D hb b hN hμ)
    (ThetaRationalMaps.CM.dense E L D hb b hN)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaRealization.CM
