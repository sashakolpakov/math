import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicSpecialLinear
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedPlaceProduct

/-! # Product -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Product.CM

noncomputable section

/-! An actual SL3(Q_q) times away group presentation of the source finite
special-unitary group, with the original rational embedding factored exactly. -/

open scoped Classical _root_.Matrix _root_.NumberField
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicPlace.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

def levels (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (Source.QuadraticConjugation.CM.Field.RealField E))) :=
  RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral (Source.QuadraticConjugation.CM.Field.RealField E) (Source.QuadraticForms.CM.hermitianForm E Q).val (.inr v)

abbrev FiniteGroup := RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (Source.QuadraticConjugation.CM.Field.RealField E) (Source.QuadraticForms.CM.hermitianForm E Q)

abbrev Away := RestrictedPlaceProduct.CM.away (levels E Q) (Source.QadicPlace.CM.place E f)

def equivalence : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × Away E Q f ≃* FiniteGroup E Q :=
  RestrictedPlaceProduct.CM.transport (levels E Q) (Source.QadicPlace.CM.place E f)
    (Source.QadicSpecialLinear.CM.equivalence E Q f)

def awayHom : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b →* Away E Q f :=
  (RestrictedPlaceProduct.CM.awayHom (levels E Q) (Source.QadicPlace.CM.place E f)).comp
    (Source.RationalLocal.CM.finiteHom E Q)

theorem equivalence_apply (a : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) (b : Away E Q f) :
    equivalence E Q f (a, b) = RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace (levels E Q) (Source.QadicPlace.CM.place E f)
      ((Source.QadicSpecialLinear.CM.equivalence E Q f).symm a) * b.val := rfl

theorem awayHom_val (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    (awayHom E Q f g).val = RestrictedPlaceProduct.CM.remove (levels E Q) (Source.QadicPlace.CM.place E f)
      (Source.RationalLocal.CM.finiteHom E Q g) := rfl

theorem inverse_rational (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    (Source.QadicSpecialLinear.CM.equivalence E Q f).symm (Matrix.SpecialLinearGroup.map f g.val) =
      Source.RationalLocal.CM.finiteHom E Q g (Source.QadicPlace.CM.place E f) := by
  exact (congrArg (Source.QadicSpecialLinear.CM.equivalence E Q f).symm
    (Source.QadicSpecialLinear.CM.rational_map E Q f g).symm).trans
      ((Source.QadicSpecialLinear.CM.equivalence E Q f).symm_apply_apply _)

theorem rational_factorization (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    equivalence E Q f (Matrix.SpecialLinearGroup.map f g.val, awayHom E Q f g) =
      Source.RationalLocal.CM.finiteHom E Q g := by
  exact (equivalence_apply E Q f _ _).trans
    ((congrArg₂ (fun a b => RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace (levels E Q) (Source.QadicPlace.CM.place E f) a * b)
      (inverse_rational E Q f g) (awayHom_val E Q f g)).trans
        (RestrictedPlaceProduct.CM.assemble_split (levels E Q) (Source.QadicPlace.CM.place E f)
          (Source.RationalLocal.CM.finiteHom E Q g)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Product.CM
