import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryMatrix
import OAI.RepresentationTheory.Theta.Adelic.RationalSU

/-! # Rational Local -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalLocal.CM

noncomputable section

/-! Actual local and finite-adelic embeddings of the original source group. -/

open scoped Classical _root_.Matrix _root_.NumberField
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

theorem hom_injective : Function.Injective (UnitaryMatrix.CM.hom E C) := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  apply (QuadraticConjugation.CM.Field.fieldEquiv E C).symm.injective
  exact congrArg (fun z => z.val.val i j) he

def localHom (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places (QuadraticConjugation.CM.Field.RealField E)) :
    Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b →*
      RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E C).val v) :=
  (RepresentationTheory.Theta.Adelic.RationalSU.rationalLocalSU (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E C) v).comp
    (UnitaryMatrix.CM.hom E C)

theorem local_matrix (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places (QuadraticConjugation.CM.Field.RealField E))
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (i j : Fin 3) :
    (localHom E C v g).val.val i j =
      RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C) v
        ((QuadraticConjugation.CM.Field.fieldEquiv E C).symm (g.val.val i j)) := rfl

def finiteHom : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b →*
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E C) :=
  (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E C)).comp
    (UnitaryMatrix.CM.hom E C)

theorem finite_matrix (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (QuadraticConjugation.CM.Field.RealField E)))
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (i j : Fin 3) :
    (finiteHom E C g v).val.val i j =
      RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C) (.inr v)
        ((QuadraticConjugation.CM.Field.fieldEquiv E C).symm (g.val.val i j)) := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalLocal.CM
