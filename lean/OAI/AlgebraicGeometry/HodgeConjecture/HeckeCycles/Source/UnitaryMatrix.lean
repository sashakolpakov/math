import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction
import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UnitaryMatrixLemmas

/-! # Unitary Matrix -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryMatrix.CM

noncomputable section

/-! The original rational special-unitary action in its actual quadratic
field coordinates. Matrix preservation is derived from the source form. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

def vector (x : GeometricSource.CM.Vec E) : Fin 3 → QuadraticForms.CM.Coefficients E C := fun i => (QuadraticConjugation.CM.Field.fieldEquiv E C).symm (x i)

def originalVector (x : Fin 3 → QuadraticForms.CM.Coefficients E C) : GeometricSource.CM.Vec E := fun i => QuadraticConjugation.CM.Field.fieldEquiv E C (x i)

theorem vector_original (x : Fin 3 → QuadraticForms.CM.Coefficients E C) : vector E C (originalVector E C x) = x := by
  funext i
  exact (QuadraticConjugation.CM.Field.fieldEquiv E C).symm_apply_apply _

theorem original_vector (x : GeometricSource.CM.Vec E) : originalVector E C (vector E C x) = x := by
  funext i
  exact (QuadraticConjugation.CM.Field.fieldEquiv E C).apply_symm_apply _

theorem form_image (x y : GeometricSource.CM.Vec E) :
    QuadraticConjugation.CM.Field.fieldEquiv E C (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue (QuadraticForms.CM.hermitianForm E C).val (vector E C x) (vector E C y)) =
      GeometricSource.CM.hermitian E B.b y x := by
  rw [QuadraticForms.CM.hermitianForm_val]
  simp only [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue, dotProduct, Matrix.mulVec_diagonal, vector,
    map_sum, map_mul, QuadraticConjugation.CM.fieldEquiv_star, AlgEquiv.apply_symm_apply]
  unfold GeometricSource.CM.hermitian
  apply Finset.sum_congr rfl
  intro i _
  change ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (x i) * ((if i = 2 then B.b else 1) * y i) = _
  ring

def matrix : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b →* (Matrix (Fin 3) (Fin 3) (QuadraticForms.CM.Coefficients E C))ˣ :=
  (Units.map ((QuadraticConjugation.CM.Field.fieldEquiv E C).symm.toRingHom.mapMatrix).toMonoidHom).comp
    (Matrix.SpecialLinearGroup.toGL.comp
      (Geometry.ComplexBall.ArithmeticQuotientEquationsData.unitarySubgroup (NumberField.IsCMField.complexConj E).toRingHom B.b).subtype)

theorem matrix_val (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    (matrix E C g).val = g.val.val.map (QuadraticConjugation.CM.Field.fieldEquiv E C).symm := rfl

theorem vector_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (x : GeometricSource.CM.Vec E) :
    (matrix E C g).val *ᵥ vector E C x =
      vector E C (ComplexAction.CM.Symplectic.rationalAction E g x) := by
  rw [matrix_val]
  funext i
  change (∑ j, (QuadraticConjugation.CM.Field.fieldEquiv E C).symm (g.val.val i j) * (QuadraticConjugation.CM.Field.fieldEquiv E C).symm (x j)) =
    (QuadraticConjugation.CM.Field.fieldEquiv E C).symm (∑ j, g.val.val i j * x j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul]

theorem form_preserves (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (x y : Fin 3 → QuadraticForms.CM.Coefficients E C) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue (QuadraticForms.CM.hermitianForm E C).val ((matrix E C g).val *ᵥ x) ((matrix E C g).val *ᵥ y) =
      RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue (QuadraticForms.CM.hermitianForm E C).val x y := by
  have h (a b : GeometricSource.CM.Vec E) :
      RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue (QuadraticForms.CM.hermitianForm E C).val ((matrix E C g).val *ᵥ vector E C a)
        ((matrix E C g).val *ᵥ vector E C b) =
      RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue (QuadraticForms.CM.hermitianForm E C).val (vector E C a) (vector E C b) := by
    apply (QuadraticConjugation.CM.Field.fieldEquiv E C).injective
    rw [vector_action, vector_action, form_image, form_image,
      ComplexAction.CM.Symplectic.rationalAction_preserves]
  simpa only [vector_original] using h (originalVector E C x) (originalVector E C y)

theorem form_matrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    (matrix E C g).val.conjTranspose * (QuadraticForms.CM.hermitianForm E C).val * (matrix E C g).val =
      (QuadraticForms.CM.hermitianForm E C).val := by
  apply Matrix.ext
  intro i j
  have h := form_preserves E C g (Pi.single i 1) (Pi.single j 1)
  rw [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue_change] at h
  simpa only [UnitaryMatrixLemmas.CM.formValue_basis] using h

theorem determinant (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) : (matrix E C g).val.det = 1 := by
  rw [matrix_val]
  change ((QuadraticConjugation.CM.Field.fieldEquiv E C).symm.toRingHom.mapMatrix g.val.val).det = 1
  rw [← RingHom.map_det, g.val.property, map_one]

theorem determinant_unit (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    Matrix.GeneralLinearGroup.det (matrix E C g) = 1 :=
  UnitaryMatrixLemmas.CM.determinant_unit (matrix E C g) (determinant E C g)

def hom : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b →*
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (QuadraticForms.CM.hermitianForm E C).val where
  toFun g := ⟨matrix E C g, form_matrix E C g, determinant_unit E C g⟩
  map_one' := Subtype.ext (map_one (matrix E C))
  map_mul' g h := Subtype.ext (map_mul (matrix E C) g h)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryMatrix.CM
