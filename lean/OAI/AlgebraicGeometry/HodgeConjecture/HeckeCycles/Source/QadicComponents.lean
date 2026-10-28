import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicPlace
import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

/-! # Qadic Components -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicComponents.CM

noncomputable section

/-! The split local quadratic coordinates are the prescribed q-adic
embedding and its conjugate, with the same labels as the source. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicPlace.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

local instance : CharZero (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion (QuadraticConjugation.CM.Field.RealField E) (.inr (QadicPlace.CM.place E f))) :=
  RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero (QuadraticConjugation.CM.Field.RealField E) (.inr (QadicPlace.CM.place E f))

def plusMap : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (.inr (QadicPlace.CM.place E f)) →+* ℚ_[q] :=
  (QadicPlace.CM.completionEquiv E f).toRingHom.comp (RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plus (QadicPlace.CM.root E Q f) (QadicPlace.CM.root_sq E Q f) (QadicPlace.CM.root_ne_zero E Q f))

def minusMap : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (.inr (QadicPlace.CM.place E f)) →+* ℚ_[q] :=
  (QadicPlace.CM.completionEquiv E f).toRingHom.comp (RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.minus (QadicPlace.CM.root E Q f) (QadicPlace.CM.root_sq E Q f) (QadicPlace.CM.root_ne_zero E Q f))

theorem plus_rational (z : QuadraticForms.CM.Coefficients E Q) :
    plusMap E Q f (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (.inr (QadicPlace.CM.place E f)) z) =
      f (QuadraticConjugation.CM.Field.fieldEquiv E Q z) := by
  change QadicPlace.CM.completionEquiv E f
    (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (QuadraticConjugation.CM.Field.RealField E) (.inr (QadicPlace.CM.place E f)) z.re + QadicPlace.CM.root E Q f *
      RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (QuadraticConjugation.CM.Field.RealField E) (.inr (QadicPlace.CM.place E f)) z.im) = f (QuadraticConjugation.CM.Field.toOriginal E Q z)
  rw [map_add, map_mul, QadicPlace.CM.completion_rational, QadicPlace.CM.completion_rational, QadicPlace.CM.root_image, QuadraticConjugation.CM.Field.toOriginal_apply, map_add, map_mul]
  change f (z.re : E) + f Q.delta * f (z.im : E) = f (z.re : E) + f (z.im : E) * f Q.delta
  ring

theorem plus_original (x : E) :
    plusMap E Q f (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (.inr (QadicPlace.CM.place E f))
      ((QuadraticConjugation.CM.Field.fieldEquiv E Q).symm x)) = f x := by
  rw [plus_rational, AlgEquiv.apply_symm_apply]

theorem minus_original (x : E) :
    minusMap E Q f (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (.inr (QadicPlace.CM.place E f))
      ((QuadraticConjugation.CM.Field.fieldEquiv E Q).symm x)) = f (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x) := by
  have hs := RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plus_star (QadicPlace.CM.root E Q f) (QadicPlace.CM.root_sq E Q f) (QadicPlace.CM.root_ne_zero E Q f)
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (.inr (QadicPlace.CM.place E f)) ((QuadraticConjugation.CM.Field.fieldEquiv E Q).symm x))
  have he := congrArg (QadicPlace.CM.completionEquiv E f) hs
  change plusMap E Q f (star _) = minusMap E Q f _ at he
  have hj (z : QuadraticForms.CM.Coefficients E Q) :
      RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (.inr (QadicPlace.CM.place E f)) (star z) =
        star (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E Q) (.inr (QadicPlace.CM.place E f)) z) :=
    RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange_star (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (QuadraticConjugation.CM.Field.RealField E) (.inr (QadicPlace.CM.place E f))) (QuadraticConjugation.CM.Field.discriminant E Q) z
  rw [← he, ← hj,
    ← QuadraticConjugation.CM.fieldEquiv_symm_conjugation, plus_original]

theorem local_matrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (i j : Fin 3) :
    plusMap E Q f ((RationalLocal.CM.localHom E Q (.inr (QadicPlace.CM.place E f)) g).val.val i j) =
      f (g.val.val i j) := by
  rw [RationalLocal.CM.local_matrix, plus_original]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicComponents.CM
