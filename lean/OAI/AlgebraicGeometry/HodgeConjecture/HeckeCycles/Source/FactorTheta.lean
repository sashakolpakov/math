import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalFactorProjection
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.Sl

/-! # Factor Theta -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorTheta

noncomputable section

section

/-! Construct the remaining factor of the actual rational source Weil
action inside the genuine finite cover. Commutation is derived from the
proved projections and uniqueness of homomorphic SL3 lifts. -/

attribute [local instance 2000] Subgroup.toGroup Prod.instGroup
open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

namespace CM.RationalWeilFactorization
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalFactorProjection.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

theorem remainder_commutes (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (u : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) :
    Commute
      (CommutingFactorization.CM.remainder (RationalFactorProjection.CM.activeLocal E f)
        (ReferenceActiveWeil.CM.Reference.lift E L.coordinates f) (WeilData.CM.finiteHom E L) g)
      (ReferenceActiveWeil.CM.Reference.lift E L.coordinates f u) :=
  CMExtraction.Finite.Sl.Local.finite_sl3_lift_commute q (WeilData.CM.weilData E places)
    (ReferenceActiveWeil.CM.Reference.lift E L.coordinates f) _
    (RationalFactorProjection.CM.remainder_commutes E L f g) u

abbrev Away := CommutingFactorization.CM.AwayWithCoordinates (RationalFactorProjection.CM.activeLocal E f)
  (ReferenceActiveWeil.CM.Reference.lift E L.coordinates f) (WeilData.CM.finiteHom E L)
  (remainder_commutes E L f)
  (SourceFinite.Product.CM.awayHom E (OppositeCoordinates.CM.coordinates E L.coordinates) f)

def away :=
  CommutingFactorization.CM.awayWithCoordinates (RationalFactorProjection.CM.activeLocal E f)
    (ReferenceActiveWeil.CM.Reference.lift E L.coordinates f) (WeilData.CM.finiteHom E L)
    (remainder_commutes E L f)
    (SourceFinite.Product.CM.awayHom E (OppositeCoordinates.CM.coordinates E L.coordinates) f)

def splitting :=
  CommutingFactorization.CM.coordinateSplitting (RationalFactorProjection.CM.activeLocal E f)
    (ReferenceActiveWeil.CM.Reference.lift E L.coordinates f) (WeilData.CM.finiteHom E L)
    (remainder_commutes E L f)
    (SourceFinite.Product.CM.awayHom E (OppositeCoordinates.CM.coordinates E L.coordinates) f)

theorem rational_recovery (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    splitting E L f (RationalFactorProjection.CM.activeLocal E f g, away E L f g) = WeilData.CM.finiteHom E L g :=
  CommutingFactorization.CM.coordinate_recovery (RationalFactorProjection.CM.activeLocal E f)
    (ReferenceActiveWeil.CM.Reference.lift E L.coordinates f) (WeilData.CM.finiteHom E L)
    (remainder_commutes E L f)
    (SourceFinite.Product.CM.awayHom E (OppositeCoordinates.CM.coordinates E L.coordinates) f) g

theorem away_coordinates (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    (away E L f g).val.1 =
      SourceFinite.Product.CM.awayHom E (OppositeCoordinates.CM.coordinates E L.coordinates) f g := rfl

theorem action_recovery (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    (WeilData.CM.weilData E places).finite.action
      (splitting E L f (RationalFactorProjection.CM.activeLocal E f g, away E L f g)) φ = WeilData.CM.finiteAction E L g φ :=
  congrArg (fun m => (WeilData.CM.weilData E places).finite.action m φ) (rational_recovery E L f g)

end CM.RationalWeilFactorization

end

/-! The constructed active/away splitting gives the literal original
source theta covariance, using exact recovery of the rational Weil lift. -/

attribute [local instance 2000] Subgroup.toGroup Prod.instGroup
open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames

namespace CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorTheta.CM.RationalWeilFactorization OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalFactorProjection.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

local instance awayGroup : Group (RationalWeilFactorization.Away E L f) := Subgroup.toGroup (RationalWeilFactorization.Away E L f)
local instance awayMulOneClass : MulOneClass (RationalWeilFactorization.Away E L f) :=
  (awayGroup E L f).toMulOneClass
local instance sourceMulOneClass :
    MulOneClass (Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × RationalWeilFactorization.Away E L f) :=
  (show Group (Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × RationalWeilFactorization.Away E L f) from Prod.instGroup).toMulOneClass

def action :=
  (WeilData.CM.weilData E places).finite.action.comp (RationalWeilFactorization.splitting E L f)

theorem action_mul (u v : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) (b c : RationalWeilFactorization.Away E L f) :
    CM.action E L f (u * v, b * c) = CM.action E L f (u, b) * CM.action E L f (v, c) :=
  (CM.action E L f).map_mul' (u, b) (v, c)

theorem rational_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    CM.action E L f (RationalFactorProjection.CM.activeLocal E f g, RationalWeilFactorization.away E L f g) φ = WeilData.CM.finiteAction E L g φ :=
  RationalWeilFactorization.action_recovery E L f g φ

theorem canonical_covariance (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    (RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L)
      (CM.action E L f (RationalFactorProjection.CM.activeLocal E f g, RationalWeilFactorization.away E L f g) φ) (UnitaryEq.CM.Frames.period E g z)).comp
        (fderiv ℂ (UnitaryEq.CM.Frames.period E g) z) =
      RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L) φ z := by
  rw [rational_action]
  exact WeilData.CM.canonical_covariance E L g φ z hz

theorem source_covariance (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places)) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (ξ : GeometricSource.CM.BallChart) :
    RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L)
      (CM.action E L f (RationalFactorProjection.CM.activeLocal E f g, RationalWeilFactorization.away E L f g) (Theta.Weil.CM.finiteWeilInput φ))
      (UnitaryEq.CM.Frames.period E g z) (fderiv ℂ (UnitaryEq.CM.Frames.period E g) z ξ) = GeometricSource.CM.thetaOneForm E L φ z ξ := by
  rw [rational_action]
  exact WeilData.CM.source_covariance E L g φ z hz ξ

end CM

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorTheta
