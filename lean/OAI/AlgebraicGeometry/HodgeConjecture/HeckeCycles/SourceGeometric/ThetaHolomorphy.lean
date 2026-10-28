import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaRationalMaps
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.CovarianceTransport

/-! # Theta Holomorphy -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaHolomorphy.CM

noncomputable section

/-! The GeometricTheta candidate inherits holomorphy and exact rational covariance
from the original source theta function and its proved finite action. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K places.count q) (hb : D.reference.b = B.b)
  {J : Type*} [Fintype J] [DecidableEq J] [Submodule.IsLattice ℚ D.reference.lattice]
  (b : Module.Basis J ℤ D.reference.lattice) (hN : 0 < D.level)
  (hμ : D.reference.μ = E.val.toRingHom)

include hμ in
theorem holomorphic : (ThetaCandidate.CM.data E L D hb b hN).HasHolomorphicThetaData := by
  have hd := ThetaRationalMaps.CM.domain E L D hb b hN hμ
  exact ⟨Eq.mpr (congrArg (fun U : Set GeometricSource.CM.BallChart =>
    DifferentiableOn ℂ (fun z => (L.period z).matrix) U) hd) L.holomorphic,
    Eq.mpr (congrArg (fun U : Set GeometricSource.CM.BallChart => DifferentiableOn ℂ (Theta.Projection.CM.projection E L) U) hd)
      (Theta.Projection.CM.projection_holomorphic E L)⟩

include hμ in
theorem covariance : (ThetaCandidate.CM.data E L D hb b hN).HasRationalThetaCovariance := by
  intro g φ z
  have hz : z.val ∈ B.domain := Eq.mp (congrArg (fun U : Set GeometricSource.CM.BallChart => z.val ∈ U)
    (ThetaRationalMaps.CM.domain E L D hb b hN hμ)) z.property
  have he := (ThetaRationalMaps.CM.action E L D hb b hN
    ((ThetaCandidate.CM.data E L D hb b hN).rationalFinite g) φ).trans
      (congrArg (fun a => Source.FactorTheta.CM.action E L
        (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)) a φ)
        (ThetaRationalMaps.CM.rational E L D hb b hN g))
  exact Theta.CovarianceTransport.CM.apply
    (RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L)) _ _ φ _ _ he
    (ThetaRationalMaps.CM.period E L D hb b hN hμ g) z.val
    (Source.FactorTheta.CM.canonical_covariance E L
      (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))
      (Rational.CoefficientTransport.CM.equivalence D.reference.b B.b hb g) φ z.val hz)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaHolomorphy.CM
