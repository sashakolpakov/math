import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELFiniteGroup
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicComponents
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicSpecialLinear
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientPadic
import OAI.RepresentationTheory.Theta.Adelic.SplitUnitary

/-! # PEL Padic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELPadic.CM

noncomputable section

/-! Evaluation of the actual PEL coefficients at a prescribed q-adic
embedding equals the corresponding native source local projection. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientPadic.TestTransport
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicPlace.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicComponents.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

local instance : CharZero (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion (QuadraticConjugation.CM.Field.RealField E) (.inr (QadicPlace.CM.place E f))) :=
  RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero (QuadraticConjugation.CM.Field.RealField E) (.inr (QadicPlace.CM.place E f))

theorem plus_continuous : Continuous (QadicComponents.CM.plusMap E Q f) :=
  (QadicPlace.CM.completion_continuous E f).comp
    (RepresentationTheory.Theta.Adelic.SplitUnitary.Continuous.plus_continuous
      (QadicPlace.CM.root E Q f) (QadicPlace.CM.root_sq E Q f) (QadicPlace.CM.root_ne_zero E Q f))

theorem coefficient (z) :
    CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E f (PELScalar.CM.equivalence E Q z) =
      QadicComponents.CM.plusMap E Q f (CMExtraction.Finite.UnitaryDet.Approximation.finiteQuadraticEvaluation (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (QadicPlace.CM.place E f) z) := by
  have he : (fun z => CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E f (PELScalar.CM.equivalence E Q z)) =
      (fun z => QadicComponents.CM.plusMap E Q f
        (CMExtraction.Finite.UnitaryDet.Approximation.finiteQuadraticEvaluation (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (QadicPlace.CM.place E f) z)) := by
    apply (CMExtraction.AdelicTensorDensity.TestTransport.denseRange_quadraticDiagonal (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q)).equalizer
      ((CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic_continuous E f).comp (PELScalar.CM.continuous E Q))
      ((plus_continuous E Q f).comp (CMExtraction.Finite.UnitaryInverse.Approximation.finiteQuadraticEvaluation_continuous (QuadraticConjugation.CM.Field.RealField E) (QadicPlace.CM.place E f)))
    funext x
    dsimp only [Function.comp_apply]
    rw [PELScalar.CM.rational, CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic_rational,
      CMExtraction.Finite.UnitaryDet.Approximation.finiteQuadraticEvaluation_rational, QadicComponents.CM.plus_rational]
  exact congr_fun he z

theorem matrix (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q)) :
    (PELFiniteGroup.CM.equivalence E Q g).val.val.map (CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E f) =
      (QadicSpecialLinear.CM.equivalence E Q f (g (QadicPlace.CM.place E f))).val := by
  rw [PELFiniteGroup.CM.matrix]
  apply Matrix.ext
  intro i j
  exact coefficient E Q f _

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELPadic.CM
