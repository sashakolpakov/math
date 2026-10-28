import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ReferenceActiveWeil
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectedCommutingRemainder

/-! # Rational Factor Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalFactorProjection.CM

noncomputable section

/-! The actual rational source Weil action and active lift project
to the same finite direct-product representation in original coordinates. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

def activeLocal : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b →* Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] :=
  (Matrix.SpecialLinearGroup.map f).comp
    (Geometry.ComplexBall.ArithmeticQuotientEquationsData.unitarySubgroup (NumberField.IsCMField.complexConj E).toRingHom B.b).subtype

def productProjection : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] ×
    SourceFinite.Product.CM.Away E (OppositeCoordinates.CM.coordinates E L.coordinates) f →*
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates).comp
    (SourceFinite.Product.CM.equivalence E (OppositeCoordinates.CM.coordinates E L.coordinates) f).toMonoidHom

theorem active_projection (u : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) :
    (WeilData.CM.weilData E places).finite.project
      (ReferenceActiveWeil.CM.Reference.lift E L.coordinates f u) = productProjection E L f (u, 1) :=
  ReferenceActiveWeil.CM.ReferenceFiniteProjection.active E L.coordinates f u

theorem rational_projection (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    (WeilData.CM.weilData E places).finite.project (WeilData.CM.finiteHom E L g) =
      productProjection E L f
        (activeLocal E f g, SourceFinite.Product.CM.awayHom E
          (OppositeCoordinates.CM.coordinates E L.coordinates) f g) :=
  (SourceFinite.FiniteLift.CM.finiteLift_covers E L (WeilData.CM.weilData E places) g).trans
    ((ReferenceActiveWeil.CM.ReferenceFiniteProjection.rational E L.coordinates g).symm.trans
      (congrArg (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates)
        (SourceFinite.Product.CM.rational_factorization E
          (OppositeCoordinates.CM.coordinates E L.coordinates) f g).symm))

theorem remainder_commutes (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (u : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) :
    Commute
      ((WeilData.CM.weilData E places).finite.project
        (CommutingFactorization.CM.remainder (activeLocal E f)
          (ReferenceActiveWeil.CM.Reference.lift E L.coordinates f) (WeilData.CM.finiteHom E L) g))
      ((WeilData.CM.weilData E places).finite.project
        (ReferenceActiveWeil.CM.Reference.lift E L.coordinates f u)) :=
  ProjectedCommutingRemainder.CM.commutes (activeLocal E f)
    (ReferenceActiveWeil.CM.Reference.lift E L.coordinates f) (WeilData.CM.finiteHom E L)
    (WeilData.CM.weilData E places).finite.project (productProjection E L f)
    (SourceFinite.Product.CM.awayHom E (OppositeCoordinates.CM.coordinates E L.coordinates) f)
    (active_projection E L f) (rational_projection E L f) g u

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalFactorProjection.CM
