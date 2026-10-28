import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MarkedAwayLevel
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.CoefficientTransport
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralOpen
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalEmbedding
import OAI.RepresentationTheory.Theta.Geometric.Data

/-! # Theta Candidate -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate

noncomputable section

/-! GeometricTheta candidate data constructed from the original source period,
original finite Weil action, actual PEL characters, and marked away level. -/

attribute [local instance 2000] Subgroup.toGroup Prod.instGroup
open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.RepresentationTheory.Theta.Geometric.Data
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalEmbedding.ParameterChoices OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.WeilData.CM

namespace CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K places.count q) (hb : D.reference.b = B.b)

local notation "A₀" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorTheta.CM.RationalWeilFactorization.Away E L
  (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))

local instance candidateAwayGroup : Group A₀ := Subgroup.toGroup A₀
local instance candidateAwayMonoid : Monoid A₀ := (candidateAwayGroup E L D).toMonoid
local instance candidateAwayMulOneClass : MulOneClass A₀ :=
  (candidateAwayGroup E L D).toMulOneClass

private theorem transportedAway_one : (Source.FactorTheta.CM.RationalWeilFactorization.away E L (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))) (((Rational.CoefficientTransport.CM.equivalence D.reference.b B.b hb).toMonoidHom) 1) = 1 :=
  (congrArg (Source.FactorTheta.CM.RationalWeilFactorization.away E L (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))) ((Rational.CoefficientTransport.CM.equivalence D.reference.b B.b hb).toMonoidHom).map_one').trans (Source.FactorTheta.CM.RationalWeilFactorization.away E L (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))).map_one'

private theorem transportedAway_mul (g h : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b) :
    (Source.FactorTheta.CM.RationalWeilFactorization.away E L (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))) (((Rational.CoefficientTransport.CM.equivalence D.reference.b B.b hb).toMonoidHom) (g * h)) = (Source.FactorTheta.CM.RationalWeilFactorization.away E L (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))) (((Rational.CoefficientTransport.CM.equivalence D.reference.b B.b hb).toMonoidHom) g) * (Source.FactorTheta.CM.RationalWeilFactorization.away E L (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))) (((Rational.CoefficientTransport.CM.equivalence D.reference.b B.b hb).toMonoidHom) h) :=
  (congrArg (Source.FactorTheta.CM.RationalWeilFactorization.away E L (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))) (((Rational.CoefficientTransport.CM.equivalence D.reference.b B.b hb).toMonoidHom).map_mul' g h)).trans
    ((Source.FactorTheta.CM.RationalWeilFactorization.away E L (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))).map_mul' (((Rational.CoefficientTransport.CM.equivalence D.reference.b B.b hb).toMonoidHom) g) (((Rational.CoefficientTransport.CM.equivalence D.reference.b B.b hb).toMonoidHom) h))

private def transportedAway :
    @MonoidHom (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b) A₀ inferInstance
      ((Subgroup.toGroup A₀).toMulOne) where
  toFun g := (Source.FactorTheta.CM.RationalWeilFactorization.away E L (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))) (((Rational.CoefficientTransport.CM.equivalence D.reference.b B.b hb).toMonoidHom) g)
  map_one' := transportedAway_one E L D hb
  map_mul' := transportedAway_mul E L D hb

variable
  {J : Type*} [Fintype J] [DecidableEq J] [Submodule.IsLattice ℚ D.reference.lattice]
  (b : Module.Basis J ℤ D.reference.lattice) (hN : 0 < D.level)

def data : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K places.count q (GeometricSource.CM.Positions E places)
    (Source.FactorTheta.CM.RationalWeilFactorization.Away E L
      (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)))
    (Source.WeilData.CM.RealCoverGroup E places) (Source.WeilData.CM.FiniteCoverGroup E places) (Source.WeilData.CM.AdelicCoverGroup E places) where
  pel := D
  localEmbedding := CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D
  away := transportedAway E L D hb
  localLevel := ⟨CMExtraction.IntegralOpen.Intrinsic.integralSL3Open q, rfl⟩
  awayLevel := Source.MarkedAwayLevel.CM.level E L D.reference hb
    (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)) b D.level hN
  weil := Source.WeilData.CM.weilData E places
  splitting := Source.FactorTheta.CM.RationalWeilFactorization.splitting E L
    (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))
  period := L.period
  project := Theta.Projection.CM.projection E L

end CM

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate
