import Lean.LibrarySuggestions.Basic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DenseSurjectiveParameter
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalDensity

/-! # Theta Rational Maps -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaRationalMaps.CM

noncomputable section

/-! The GeometricTheta candidate has the original source active/away rational
map, the original finite action, and the original ball period map. -/

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

theorem rational (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b) :
    (ThetaCandidate.CM.data E L D hb b hN).rationalFinite g =
      Source.RationalAwayTopology.CM.rational E L
        (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))
        (Rational.CoefficientTransport.CM.equivalence D.reference.b B.b hb g) := by
  apply Prod.ext
  · exact congrArg (Matrix.SpecialLinearGroup.map (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)))
      (Rational.CoefficientTransport.CM.matrix D.reference.b B.b hb g).symm
  · rfl

theorem action (a) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    (ThetaCandidate.CM.data E L D hb b hN).finiteWeil a φ =
      Source.FactorTheta.CM.action E L (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)) a φ := rfl

theorem dense : DenseRange (ThetaCandidate.CM.data E L D hb b hN).rationalFinite :=
  DenseSurjectiveParameter.CM.dense
    (Source.RationalAwayTopology.CM.rational E L (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)))
    (Source.RationalDensity.CM.dense E L (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)))
    (Rational.CoefficientTransport.CM.equivalence D.reference.b B.b hb)
    (Rational.CoefficientTransport.CM.equivalence D.reference.b B.b hb).surjective
    (ThetaCandidate.CM.data E L D hb b hN).rationalFinite (rational E L D hb b hN)

theorem domain (hμ : D.reference.μ = E.val.toRingHom) :
    ((ThetaCandidate.CM.data E L D hb b hN).domain : Set GeometricSource.CM.BallChart) = B.domain := by
  change (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (D.reference.μ D.reference.b) : Set GeometricSource.CM.BallChart) = B.domain
  rw [hμ, hb]
  rfl

theorem period (hμ : D.reference.μ = E.val.toRingHom) (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b) :
    (ThetaCandidate.CM.data E L D hb b hN).periodMap g =
      Source.UnitaryEq.CM.Frames.period E
        (Rational.CoefficientTransport.CM.equivalence D.reference.b B.b hb g) := by
  have h₁ := Rational.CoefficientTransport.CM.period D.reference.b B.b hb D.reference.μ g
  have h₂ := congrArg (fun μ : E →+* ℂ => RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm B.b μ
    (Rational.CoefficientTransport.CM.equivalence D.reference.b B.b hb g)) hμ
  exact congrArg (fun e : Equiv.Perm GeometricSource.CM.BallChart => fun z => e z) (h₁.trans h₂)

--
--

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaRationalMaps.CM
