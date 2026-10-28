import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaFiniteCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaHolomorphy
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ReferenceAwayFixed
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductFixedVectors
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ReferenceFrame

/-! # Projective Geometric Theta Prepared -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectiveGeometricThetaPrepared.CM

noncomputable section

/-! The original source candidate is spherical on the matched reference
level. Its actual descended theta form removes the away scalar, and the
proved prime bound removes the integral active scalar. -/

open scoped Classical _root_.NumberField _root_.Manifold
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K places.count q) (hb : D.reference.b = B.b)
  {J : Type*} [Fintype J] [DecidableEq J] [Submodule.IsLattice ℚ D.reference.lattice]
  (b : Module.Basis J ℤ D.reference.lattice) (hN : 0 < D.level)

omit [IsGalois ℚ E] in
theorem spherical (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
    (hK : D.reference.adelicPrincipalLevel D.level ≤
      (Source.ProjectiveLevel.CM.level E L D.reference hb
        (Theta.Weil.CM.finiteWeilInput φ)).toSubgroup)
    (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice D.reference.lattice)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : B.Domain → X.analyticSpace)
    (hπ : (CoverFactor.CM.withLattice E B D.reference.lattice hΛ.1 hΛ.2.1 hΛ.2.2).IsBallCover D.level X π)
    (ω : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (hω : GeometricSource.CM.RepresentsTheta E L φ X π ω)
    (hne : ∃ z ∈ B.domain, ∃ ξ, GeometricSource.CM.thetaOneForm E L φ z ξ ≠ 0)
    (ha : ∀ u ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q, Source.FactorTheta.CM.action E L
      (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)) (u, 1)
        (Theta.Weil.CM.finiteWeilInput φ) = Theta.Weil.CM.finiteWeilInput φ) :
    Theta.Weil.CM.finiteWeilInput φ ∈ (SourceGeometric.ThetaCandidate.CM.data E L D hb b hN).sphericalInputs := by
  intro a ha'
  exact ProductFixedVectors.CM.fixed
    (Source.FactorTheta.CM.action E L (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)))
    (Theta.Weil.CM.finiteWeilInput φ) a.1 a.2 (ha a.1 ha'.1)
    (Source.ReferenceAwayFixed.CM.fixed E L D.reference hb hΛ
      (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)) b D.level hN
      φ hK X π hπ ω hω hne ha a.2 ha'.2)

theorem at_prime (hμ : D.reference.μ = E.val.toRingHom)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
    (hK : D.reference.adelicPrincipalLevel D.level ≤
      (Source.ProjectiveLevel.CM.level E L D.reference hb
        (Theta.Weil.CM.finiteWeilInput φ)).toSubgroup)
    (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice D.reference.lattice)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : B.Domain → X.analyticSpace)
    (hπ : (CoverFactor.CM.withLattice E B D.reference.lattice hΛ.1 hΛ.2.1 hΛ.2.2).IsBallCover D.level X π)
    (ω : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (hω : GeometricSource.CM.RepresentsTheta E L φ X π ω)
    (hne : ∃ z ∈ B.domain, ∃ ξ, GeometricSource.CM.thetaOneForm E L φ z ξ ≠ 0)
    (hprime :
      (∀ (f : E →+* ℚ_[q]) (u : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q), u ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q →
        Source.FactorTheta.CM.action E L f (u, 1) (Theta.Weil.CM.finiteWeilInput φ) =
          Theta.Weil.CM.finiteWeilInput φ) ∧
      (∀ (τ : E →+* ℚ_[q]) (χ : NumberField.RingOfIntegers E →+* ℤ_[q]),
        (∀ a : NumberField.RingOfIntegers E, τ a = (χ a : ℚ_[q])) →
        Local.Lattice.CM.localLattice τ D.reference.lattice = Local.Lattice.CM.standard (q := q))) :
    (SourceGeometric.ThetaCandidate.CM.data E L D hb b hN).HasFiniteCoordinates ∧
    (SourceGeometric.ThetaCandidate.CM.data E L D hb b hN).HasHolomorphicThetaData ∧
    (SourceGeometric.ThetaCandidate.CM.data E L D hb b hN).HasRationalThetaCovariance ∧
    DenseRange (SourceGeometric.ThetaCandidate.CM.data E L D hb b hN).rationalFinite ∧
    Theta.Weil.CM.finiteWeilInput φ ∈ (SourceGeometric.ThetaCandidate.CM.data E L D hb b hN).sphericalInputs :=
  ⟨SourceGeometric.ThetaFiniteCoordinates.CM.coordinates E L D hb b hN hg hq
      (Intrinsic.ReferenceFrame.CM.IntrinsicReference.standard D hprime.2),
    SourceGeometric.ThetaHolomorphy.CM.holomorphic E L D hb b hN hμ,
    SourceGeometric.ThetaHolomorphy.CM.covariance E L D hb b hN hμ,
    SourceGeometric.ThetaRationalMaps.CM.dense E L D hb b hN,
    spherical E L D hb b hN φ hK hΛ X π hπ ω hω hne
      (hprime.1 (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)))⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectiveGeometricThetaPrepared.CM
