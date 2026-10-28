import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Topology
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEquiv
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedAwayComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveAwayProjection

/-! # Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.Projection.CM

noncomputable section

/-! The source's actual selected local projection and complementary
restricted product, with exact rational-coordinate identities. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveAwayProjection.Approximation

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicPlace.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Product.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

abbrev Away := CMExtraction.RestrictedAwaySame.Approximation.RestrictedAway
  (fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (Source.QuadraticConjugation.CM.Field.RealField E) =>
    RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral (Source.QuadraticConjugation.CM.Field.RealField E) (Source.QuadraticForms.CM.hermitianForm E C).val (.inr v))
  (Source.QadicPlace.CM.place E f)

def localProjection : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (Source.QuadraticConjugation.CM.Field.RealField E) (Source.QuadraticForms.CM.hermitianForm E C).val (.inr (Source.QadicPlace.CM.place E f))) →ₜ*
      Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] :=
  ⟨(Source.QadicSpecialLinear.CM.equivalence E C f).toMonoidHom,
    Source.QadicTopology.CM.equivalence_continuous E C f⟩

def projection :=
  CMExtraction.ActiveAwayProjection.Approximation.activeAwayProjection (Source.QuadraticConjugation.CM.Field.RealField E) (d := Source.QuadraticConjugation.CM.Field.discriminant E C)
    (Source.QuadraticForms.CM.hermitianForm E C) (Source.QadicPlace.CM.place E f) (localProjection E C f)

def rational :=
  (CMExtraction.ActiveAwayProjection.Approximation.activeAwayProjection (Source.QuadraticConjugation.CM.Field.RealField E) (d := Source.QuadraticConjugation.CM.Field.discriminant E C)
    (Source.QuadraticForms.CM.hermitianForm E C) (Source.QadicPlace.CM.place E f) (localProjection E C f)).toMonoidHom.comp
      ((RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (Source.QuadraticConjugation.CM.Field.RealField E) (Source.QuadraticForms.CM.hermitianForm E C)).comp
        (Source.UnitaryMatrix.CM.hom E C))

theorem rational_first (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    (rational E C f g).1 = Matrix.SpecialLinearGroup.map f g.val :=
  Source.QadicSpecialLinear.CM.rational_map E C f g

theorem rational_away (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    (rational E C f g).2 = RestrictedAwayComparison.CM.forget (SourceFinite.Product.CM.levels E C) (Source.QadicPlace.CM.place E f)
      (SourceFinite.Product.CM.awayHom E C f g) :=
  (RestrictedAwayComparison.CM.forget_remove (SourceFinite.Product.CM.levels E C) (Source.QadicPlace.CM.place E f)
    (Source.RationalLocal.CM.finiteHom E C g)).symm

theorem rational_range : Set.range (rational E C f) =
    Set.range (fun g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (Source.QuadraticForms.CM.hermitianForm E C).val =>
      projection E C f (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU
        (Source.QuadraticConjugation.CM.Field.RealField E) (Source.QuadraticForms.CM.hermitianForm E C) g)) := by
  let t := fun g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (Source.QuadraticForms.CM.hermitianForm E C).val =>
    projection E C f (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU
      (Source.QuadraticConjugation.CM.Field.RealField E) (Source.QuadraticForms.CM.hermitianForm E C) g)
  change Set.range (t ∘ Source.UnitaryEquiv.CM.equivalence E C) = Set.range t
  exact (Source.UnitaryEquiv.CM.equivalence E C).surjective.range_comp t

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.Projection.CM
