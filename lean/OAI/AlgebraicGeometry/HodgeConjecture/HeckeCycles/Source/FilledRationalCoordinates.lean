import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledSupport
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoefficientVectorCoordinates

/-! # Filled Rational Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledRationalCoordinates.CM

noncomputable section

/-! Every rational-basis coordinate of the filled source PEL action
agrees with the original rational action at primes different from q. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoefficientVectorCoordinates.TestTransport

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hb : P.b = B.b)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])
  {J : Type*} [Fintype J] [DecidableEq J] (e : (Fin 3 → E) ≃ₗ[ℚ] (J → ℚ))

theorem other (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (x : Fin 3 → E) (j : J)
    (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) :
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (CMExtraction.CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e
      ((FilledLocal.CM.PEL.hom E Q P hb f g).val (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x)) j) =
        algebraMap ℚ ℚ_[p] (e (g.val.val *ᵥ x) j) := by
  have he := FilledSupport.CM.other_coordinate E Q P hb f
    (RationalLocal.CM.finiteHom E Q g) (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x)
    ((LinearMap.proj j).comp (CMExtraction.CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e).toLinearMap) p hpq
  have hr := congrArg (fun y : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E =>
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (CMExtraction.CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e y j))
    (PELFiniteGroup.CM.Matrix.rational_vector E Q P hb g x)
  have hc := congrArg (fun y : J → AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles => RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (y j))
    (CMExtraction.CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates_rational E e (g.val.val *ᵥ x))
  exact he.trans (hr.trans (hc.trans ((RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).commutes _)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledRationalCoordinates.CM
