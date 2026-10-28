import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaComplexComponents
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalNormalization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.BallNormalization

/-! # Theta Compact Components -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaCompactComponents.CM.ComponentValues

/-! The complex comparison uses explicit nonzero real diagonal factors.
At the distinguished place its last factor is the actual ball radius. -/

open scoped Classical _root_.NumberField _root_.Matrix Kronecker
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanForms.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaComplexComponents.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

def coefficient (v : Fin places.count) (ij : Fin 3 × Fin 1) : ℝ :=
  Real.sqrt |Source.ArchimedeanForms.CM.hermitianReal E (B := B) v ij.1| *
    Real.sqrt |Source.ArchimedeanForms.CM.skewReal E (OppositeCoordinates.CM.coordinates E L.coordinates) v|

theorem coefficient_pos (v : Fin places.count) (ij : Fin 3 × Fin 1) :
    0 < coefficient E L v ij :=
  mul_pos (Real.sqrt_pos.mpr (abs_pos.mpr (Source.ArchimedeanForms.CM.hermitian_ne_zero E v ij.1)))
    (Real.sqrt_pos.mpr (abs_pos.mpr (Source.ArchimedeanForms.CM.skew_ne_zero E
      (OppositeCoordinates.CM.coordinates E L.coordinates) v)))

theorem coefficient_ne_zero (v : Fin places.count) (ij : Fin 3 × Fin 1) :
    (coefficient E L v ij : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (coefficient_pos E L v ij))

theorem matrix_diagonal (v : Fin places.count) :
    ThetaComplexComponents.CM.matrix E L v = Matrix.diagonal (fun ij => (coefficient E L v ij : ℂ)) :=
  DiagonalNormalization.CM.Values.tensor (Source.ArchimedeanForms.CM.hermitianReal E (B := B) v)
    (fun _ : Fin 1 => Source.ArchimedeanForms.CM.skewReal E (OppositeCoordinates.CM.coordinates E L.coordinates) v)
    (Source.ArchimedeanForms.CM.hermitian_ne_zero E v)
    (fun _ => Source.ArchimedeanForms.CM.skew_ne_zero E (OppositeCoordinates.CM.coordinates E L.coordinates) v)

theorem matrix_star (v : Fin places.count) : (ThetaComplexComponents.CM.matrix E L v).map star = ThetaComplexComponents.CM.matrix E L v := by
  rw [matrix_diagonal, Matrix.diagonal_map (star_zero ℂ)]
  exact congrArg Matrix.diagonal (funext fun ij => Complex.conj_ofReal (coefficient E L v ij))

theorem standard (w : GeometricSource.CM.Ambient E) (v : Fin places.count) (ij : Fin 3 × Fin 1) :
    (ThetaComplexComponents.CM.components E L w v).1 ij = (coefficient E L v ij : ℂ) * w (places.representative v) ij.1 := by
  change (ThetaComplexComponents.CM.matrix E L v).mulVec _ ij = _
  rw [matrix_diagonal, Matrix.mulVec_diagonal]
  rfl

theorem dual (w : GeometricSource.CM.Ambient E) (v : Fin places.count) (ij : Fin 3 × Fin 1) :
    (ThetaComplexComponents.CM.components E L w v).2 ij = ThetaComplexComponents.CM.sign E L v ij * (coefficient E L v ij : ℂ) *
      w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative v) ij.1 := by
  change ThetaComplexComponents.CM.sign E L v ij * (((ThetaComplexComponents.CM.matrix E L v).map star).mulVec _ ij) = _
  rw [matrix_star, matrix_diagonal, Matrix.mulVec_diagonal]
  exact (mul_assoc _ _ _).symm

theorem distinguished_hermitian (i : Fin 3) :
    Source.ArchimedeanForms.CM.hermitianReal E (B := B) places.distinguished i = if i = 2 then (B.b : ℂ).re else 1 := by
  change (ReferenceDatum.CM.embeddings E places places.distinguished
    (Source.QuadraticForms.CM.coefficient E i)).re = _
  rw [ReferenceDatum.CM.embeddings_distinguished]
  by_cases hi : i = 2
  · simp only [Source.QuadraticForms.CM.coefficient, ite_eq_left hi]
    rfl
  · simp only [Source.QuadraticForms.CM.coefficient, ite_eq_right hi]
    change (E.val (1 : E)).re = 1
    rw [map_one, Complex.one_re]

theorem distinguished_coefficient (ij : Fin 3 × Fin 1) :
    coefficient E L places.distinguished ij =
      (if ij.1 = 2 then Source.BallNormalization.CM.radius E B else 1) *
        Real.sqrt |Source.ArchimedeanForms.CM.skewReal E (OppositeCoordinates.CM.coordinates E L.coordinates) places.distinguished| := by
  unfold coefficient
  rw [distinguished_hermitian]
  by_cases hi : ij.1 = 2
  · rw [ite_eq_left hi, abs_of_neg B.negative, ite_eq_left hi]
    rfl
  · simp [hi]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaCompactComponents.CM.ComponentValues

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaCompactComponents.CM

/-! At compact places the actual nonzero diagonal comparison preserves
exactly the source's selected CM component. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaComplexComponents.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaCompactComponents.CM.ComponentValues

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

theorem sign_ne_zero (v : Fin places.count) (ij : Fin 3 × Fin 1) : ThetaComplexComponents.CM.sign E L v ij ≠ 0 := by
  unfold ThetaComplexComponents.CM.sign
  split_ifs <;> norm_num

theorem standard_zero (w : GeometricSource.CM.Ambient E) (v : Fin places.count) (j : Fin 1) :
    (∀ i, (ThetaComplexComponents.CM.components E L w v).1 (i, j) = 0) ↔ w (places.representative v) = 0 := by
  constructor
  · intro h
    funext i
    have hi := h i
    rw [ComponentValues.standard, mul_eq_zero] at hi
    exact hi.resolve_left (ComponentValues.coefficient_ne_zero E L v (i, j))
  · intro h i
    rw [ComponentValues.standard, h]
    exact mul_zero _

theorem dual_zero (w : GeometricSource.CM.Ambient E) (v : Fin places.count) (j : Fin 1) :
    (∀ i, (ThetaComplexComponents.CM.components E L w v).2 (i, j) = 0) ↔
      w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative v) = 0 := by
  constructor
  · intro h
    funext i
    have hi := h i
    rw [ComponentValues.dual, mul_eq_zero] at hi
    exact hi.resolve_left (mul_ne_zero (sign_ne_zero E L v (i, j)) (ComponentValues.coefficient_ne_zero E L v (i, j)))
  · intro h i
    rw [ComponentValues.dual, h]
    exact mul_zero _

theorem selected (w : GeometricSource.CM.Ambient E) (v : Fin places.count) (hv : v ≠ places.distinguished) (j : Fin 1) :
    (if (Source.BallArithmetic.CM.data E L).positive v j then
      (∀ i, (ThetaComplexComponents.CM.components E L w v).2 (i, j) = 0)
      else (∀ i, (ThetaComplexComponents.CM.components E L w v).1 (i, j) = 0)) ↔
    (if d (places.representative v) then w (places.representative v) = 0
      else w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative v) = 0) := by
  have hp : (Source.BallArithmetic.CM.data E L).positive v j = !(d (places.representative v)) := by
    change (if v = places.distinguished then false else !(d (places.representative v))) = _
    rw [ite_eq_right hv]
  rw [hp]
  cases hd : d (places.representative v)
  · simpa only [Bool.not_false, Bool.false_eq_true, ite_false, ite_true] using dual_zero E L w v j
  · simpa only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true] using standard_zero E L w v j

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaCompactComponents.CM

end

end OAI
