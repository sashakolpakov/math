import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicSpecialLinear
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitMatrixTopology
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialLinearFieldEquiv

/-! # Qadic Topology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicTopology.CM

noncomputable section

/-! The prescribed q-adic identification of the source local group is a homeomorphism. -/

open scoped Classical _root_.Matrix _root_.NumberField
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicPlace.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicSpecialLinear.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

local instance : CharZero (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion (QuadraticConjugation.CM.Field.RealField E) (.inr (QadicPlace.CM.place E f))) :=
  RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero (QuadraticConjugation.CM.Field.RealField E) (.inr (QadicPlace.CM.place E f))

def homeomorphism : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (QadicSpecialLinear.CM.localForm E Q f).val ≃ₜ
    Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] :=
  (SplitMatrixTopology.CM.SpecialUnitary.homeomorphism (QadicPlace.CM.root E Q f) (QadicPlace.CM.root_sq E Q f) (QadicPlace.CM.root_ne_zero E Q f)
    (QadicSpecialLinear.CM.localForm E Q f) (QadicSpecialLinear.CM.local_hermitian E Q f)).trans
    (SpecialLinearFieldEquiv.CM.Topology.homeomorphism (QadicPlace.CM.completionEquiv E f)
      (QadicPlace.CM.completion_continuous E f) (QadicPlace.CM.completion_inverse_continuous E f))

theorem homeomorphism_apply (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (QadicSpecialLinear.CM.localForm E Q f).val) :
    homeomorphism E Q f g = QadicSpecialLinear.CM.equivalence E Q f g := rfl

theorem equivalence_continuous : Continuous (QadicSpecialLinear.CM.equivalence E Q f) := (homeomorphism E Q f).continuous

theorem inverse_continuous : Continuous (QadicSpecialLinear.CM.equivalence E Q f).symm := (homeomorphism E Q f).symm.continuous

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicTopology.CM
