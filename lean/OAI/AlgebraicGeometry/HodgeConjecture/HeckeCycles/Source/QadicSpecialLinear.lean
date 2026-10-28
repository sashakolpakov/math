import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicComponents
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.GlobalFrames
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialLinearFieldEquiv
import OAI.RepresentationTheory.Theta.Adelic.SplitUnitary

/-! # Qadic Special Linear -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicSpecialLinear.CM

noncomputable section

/-! The actual split local source group is SL3(Q_q), with its rational
matrices equal to the prescribed q-adic embedding entry by entry. -/

open scoped Classical _root_.Matrix _root_.NumberField
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicPlace.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

local instance : CharZero (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion (QuadraticConjugation.CM.Field.RealField E) (.inr (QadicPlace.CM.place E f))) :=
  RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero (QuadraticConjugation.CM.Field.RealField E) (.inr (QadicPlace.CM.place E f))

def localForm : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (.inr (QadicPlace.CM.place E f))))ˣ :=
  RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (QuadraticForms.CM.hermitianForm E Q) (.inr (QadicPlace.CM.place E f))

theorem local_hermitian : (localForm E Q f).val.conjTranspose = (localForm E Q f).val := by
  have hj (z : QuadraticForms.CM.Coefficients E Q) :
      RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (.inr (QadicPlace.CM.place E f)) (star z) =
        star (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (.inr (QadicPlace.CM.place E f)) z) :=
    RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange_star (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (QuadraticConjugation.CM.Field.RealField E) (.inr (QadicPlace.CM.place E f))) (QuadraticConjugation.CM.Field.discriminant E Q) z
  change ((QuadraticForms.CM.hermitianForm E Q).val.map (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (.inr (QadicPlace.CM.place E f)))).conjTranspose = _
  rw [← RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.map_conjTranspose _ hj, QuadraticForms.CM.hermitianForm_hermitian]
  rfl

def equivalence : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (localForm E Q f).val ≃*
    Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] :=
  (RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL
    (QadicPlace.CM.root E Q f) (QadicPlace.CM.root_sq E Q f) (QadicPlace.CM.root_ne_zero E Q f) (localForm E Q f) (local_hermitian E Q f)).trans
      (SpecialLinearFieldEquiv.CM.map (QadicPlace.CM.completionEquiv E f))

theorem rational_matrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (i j : Fin 3) :
    (equivalence E Q f (RationalLocal.CM.localHom E Q (.inr (QadicPlace.CM.place E f)) g)).val i j =
      f (g.val.val i j) :=
  QadicComponents.CM.local_matrix E Q f g i j

theorem rational_map (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    equivalence E Q f (RationalLocal.CM.localHom E Q (.inr (QadicPlace.CM.place E f)) g) =
      Matrix.SpecialLinearGroup.map f g.val := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  exact rational_matrix E Q f g i j

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicSpecialLinear.CM
