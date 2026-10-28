import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaCompactComponents
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeightedBallComponents

/-! # Theta Distinguished Basis -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaDistinguishedBasis.CM.Components

/-! At the distinguished place the actual component comparison carries
the source weighted line and Hermitian annihilator to AdelicTheta's line and dual. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.BallNormalization.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaComplexComponents.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanForms.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

def scale : ℂ :=
  Real.sqrt |Source.ArchimedeanForms.CM.skewReal E (OppositeCoordinates.CM.coordinates E L.coordinates) places.distinguished|

theorem scale_ne_zero : scale E L ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr
    (abs_pos.mpr (Source.ArchimedeanForms.CM.skew_ne_zero E (OppositeCoordinates.CM.coordinates E L.coordinates) places.distinguished))))

include places in
theorem coefficient_radius : (B.b : ℂ) = -(Source.BallNormalization.CM.radius E B : ℂ) ^ 2 := by
  have hi := Source.ArchimedeanForms.CM.real_element E B.b B.conjugate_b (places := places) places.distinguished
  rw [ReferenceDatum.CM.embeddings_distinguished] at hi
  change (B.b : ℂ).im = 0 at hi
  apply Complex.ext
  · simp only [Complex.neg_re, pow_two, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    have h := Source.BallNormalization.CM.radius_square E B
    nlinarith
  · simpa only [Complex.neg_im, pow_two, Complex.mul_im, Complex.ofReal_im,
      mul_zero, zero_mul, add_zero, neg_zero] using hi

theorem standard (w : GeometricSource.CM.Ambient E) (j : Fin 1) :
    (fun i => (ThetaComplexComponents.CM.components E L w places.distinguished).1 (i, j)) =
      WeightedBallComponents.CM.standard (Source.BallNormalization.CM.radius E B : ℂ) (scale E L)
        (w (places.representative places.distinguished)) := by
  funext i
  rw [ThetaCompactComponents.CM.ComponentValues.standard, ThetaCompactComponents.CM.ComponentValues.distinguished_coefficient]
  change (((if i = 2 then Source.BallNormalization.CM.radius E B else 1) *
    Real.sqrt |Source.ArchimedeanForms.CM.skewReal E (OppositeCoordinates.CM.coordinates E L.coordinates) places.distinguished| : ℝ) : ℂ) *
      w (places.representative places.distinguished) i =
    (if i = 2 then (Source.BallNormalization.CM.radius E B : ℂ) else 1) * scale E L * w (places.representative places.distinguished) i
  by_cases hi : i = 2
  · simp only [ite_eq_left hi, Complex.ofReal_mul]
    rfl
  · simp only [ite_eq_right hi, Complex.ofReal_mul, Complex.ofReal_one]
    rfl

theorem dual (w : GeometricSource.CM.Ambient E) (j : Fin 1) :
    (fun i => (ThetaComplexComponents.CM.components E L w places.distinguished).2 (i, j)) =
      WeightedBallComponents.CM.dual (Source.BallNormalization.CM.radius E B : ℂ) (scale E L)
        (w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative places.distinguished)) := by
  funext i
  rw [ThetaCompactComponents.CM.ComponentValues.dual, ThetaCompactComponents.CM.ComponentValues.distinguished_coefficient]
  have hp : (Source.BallArithmetic.CM.data E L).positive places.distinguished j = false :=
    (Source.BallArithmetic.CM.data E L).distinguished_sign j
  unfold ThetaComplexComponents.CM.sign
  rw [hp]
  by_cases hi : i = 2
  · simp [hi, WeightedBallComponents.CM.dual, scale]
  · simp [hi, WeightedBallComponents.CM.dual, scale]

theorem line_iff (z : GeometricSource.CM.BallChart) (w : GeometricSource.CM.Ambient E) (j : Fin 1) :
    (∃ c : ℂ, ∀ i, (ThetaComplexComponents.CM.components E L w places.distinguished).1 (i, j) =
      RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector (Source.BallNormalization.CM.normalize E B z) i * c) ↔
      w (places.representative places.distinguished) ∈ ℂ ∙ GeometricSource.CM.BallDatum.lineVector z := by
  have he := standard E L w j
  simp only [funext_iff] at he
  simp only [he]
  exact WeightedBallComponents.CM.line_iff (Source.BallNormalization.CM.radius E B : ℂ) (scale E L)
    (Complex.ofReal_ne_zero.mpr (Source.BallNormalization.CM.radius_ne_zero E B)) (scale_ne_zero E L) z _

theorem source_pairing (z : GeometricSource.CM.BallChart) (y : GeometricSource.CM.Vec ℂ) :
    GeometricSource.CM.localPairing E B.b (places.representative places.distinguished) (GeometricSource.CM.BallDatum.lineVector z) y =
      z 0 * y 0 + z 1 * y 1 - (Source.BallNormalization.CM.radius E B : ℂ) ^ 2 * y 2 := by
  rw [places.identity]
  simp [GeometricSource.CM.localPairing, GeometricSource.CM.BallDatum.lineVector, Fin.sum_univ_succ,
    coefficient_radius E (B := B) (places := places)]
  ring

theorem annihilator_iff (z : GeometricSource.CM.BallChart) (w : GeometricSource.CM.Ambient E) (j : Fin 1) :
    dotProduct (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector (Source.BallNormalization.CM.normalize E B z))
      (fun i => (ThetaComplexComponents.CM.components E L w places.distinguished).2 (i, j)) = 0 ↔
      GeometricSource.CM.localPairing E B.b (places.representative places.distinguished) (GeometricSource.CM.BallDatum.lineVector z)
        (w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative places.distinguished)) = 0 := by
  rw [dual, source_pairing E (B := B) (places := places)]
  exact WeightedBallComponents.CM.annihilator_iff (Source.BallNormalization.CM.radius E B : ℂ) (scale E L)
    (Complex.ofReal_ne_zero.mpr (Source.BallNormalization.CM.radius_ne_zero E B)) (scale_ne_zero E L) z _

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaDistinguishedBasis.CM.Components

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaDistinguishedBasis.CM

/-! The actual distinguished orthonormal basis normalizes the weighted
source negative line by precisely the source ball radius. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.BallNormalization.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  (B : GeometricSource.CM.BallDatum E) (places : GeometricSource.CM.Places E)

theorem inverse_matrix :
    (Source.ArchimedeanBases.CM.hermitian E (B := B) places.distinguished).inv =
      Matrix.diagonal (fun i : Fin 3 => if i = 2 then (Source.BallNormalization.CM.radius E B : ℂ) else 1) := by
  rw [Source.ArchimedeanBases.CM.hermitian, DiagonalNormalization.CM.Values.inverse]
  congr 1
  funext i
  rw [ThetaCompactComponents.CM.ComponentValues.distinguished_hermitian]
  by_cases hi : i = 2
  · rw [ite_eq_left hi, abs_of_neg B.negative, ite_eq_left hi]
    rfl
  · simp [hi]

theorem line_coordinates (z : GeometricSource.CM.BallChart) :
    (Source.ArchimedeanBases.CM.hermitian E (B := B) places.distinguished).inv.mulVec
      (GeometricSource.CM.BallDatum.lineVector z) =
        (Source.BallNormalization.CM.radius E B : ℂ) • RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector (Source.BallNormalization.CM.normalize E B z) := by
  rw [inverse_matrix]
  funext i
  rw [Matrix.mulVec_diagonal]
  have h := congrFun (WeightedBallComponents.CM.standard_line (Source.BallNormalization.CM.radius E B : ℂ) 1
    (Complex.ofReal_ne_zero.mpr (Source.BallNormalization.CM.radius_ne_zero E B)) z) i
  change (if i = 2 then (Source.BallNormalization.CM.radius E B : ℂ) else 1) * GeometricSource.CM.BallDatum.lineVector z i =
    ((Source.BallNormalization.CM.radius E B : ℂ) • RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector (fun j => z j / (Source.BallNormalization.CM.radius E B : ℂ))) i
  simpa only [WeightedBallComponents.CM.standard, LinearMap.coe_mk, AddHom.coe_mk, mul_one] using h

theorem inverse_line_coordinates (z : GeometricSource.CM.BallChart) :
    (Source.ArchimedeanBases.CM.hermitian E (B := B) places.distinguished).val.mulVec
      (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector (Source.BallNormalization.CM.normalize E B z)) =
        (Source.BallNormalization.CM.radius E B : ℂ)⁻¹ • GeometricSource.CM.BallDatum.lineVector z := by
  have h := congrArg
    (Matrix.mulVec (Source.ArchimedeanBases.CM.hermitian E (B := B) places.distinguished).val)
    (line_coordinates E B places z)
  rw [Matrix.mulVec_mulVec,
    (Source.ArchimedeanBases.CM.hermitian E (B := B) places.distinguished).val_inv,
    Matrix.one_mulVec, Matrix.mulVec_smul] at h
  rw [h, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Source.BallNormalization.CM.radius_ne_zero E B)), one_smul]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaDistinguishedBasis.CM

end

end OAI
