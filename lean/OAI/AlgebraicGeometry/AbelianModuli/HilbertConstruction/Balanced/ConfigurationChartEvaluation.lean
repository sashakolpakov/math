import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameChartNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.AwayEvaluation

/-! # Configuration Chart Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.ConfigurationChartEvaluation

noncomputable section

/-! A vector configuration on which the chart denominator is invertible
defines a ring point of the balanced chart. Its coordinates satisfy the
determinant normalization equations over any commutative ring. -/
open scoped Classical
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] {r m : ℕ}

def balancedConfigurationPolynomialEvaluation (w : Fin m → Fin r → A) :
    DeterminantAlgebra.balancedDeterminantAlgebra R r m →ₐ[R] A :=
  (MvPolynomial.aeval (fun jk : Fin m × Fin r => w jk.1 jk.2)).comp
    (DeterminantAlgebra.balancedDeterminantAlgebra R r m).val

theorem balancedConfigurationPolynomialEvaluation_denominator
    (w : Fin m → Fin r → A) (a : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight) :
    balancedConfigurationPolynomialEvaluation (R := R) w (FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha) =
      MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) a := by
  change MvPolynomial.aeval (fun jk : Fin m × Fin r => w jk.1 jk.2)
    (MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) a) = _
  simp only [MonomialAlgebra.exponentMonomial, map_prod, map_pow, LabeledDeterminantPolynomials.labeledDeterminantPolynomial_eval]

def balancedConfigurationChartEvaluation (i : Fin m) (w : Fin m → Fin r → A)
    (a : (Fin r → Fin m) → ℕ) (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hw : IsUnit (MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) a)) :
    FrameChartCoordinates.balancedDeterminantChartRing R i a ha →+* A :=
  Homogeneous.AwayEvaluation.homogeneousAwayEvaluation (DeterminantGrading.balancedDeterminantGrading R r m i)
    (FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha)
    (balancedConfigurationPolynomialEvaluation (R := R) w).toRingHom
    ((balancedConfigurationPolynomialEvaluation_denominator (R := R) w a ha).symm ▸ hw)

theorem balancedConfigurationChartEvaluation_frame_cross
    (i : Fin m) (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r)
    (a : (Fin r → Fin m) → ℕ) (C : Fin m → (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : ∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a)
    (w : Fin m → Fin r → A) (hw : IsUnit (MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) a))
    (z : Fin m) (k : Fin r) :
    balancedConfigurationChartEvaluation (R := R) i w a ha hw
        (FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC z k) *
        DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun A (Fin r)) (fun j => w (σ j)) (w e) (w z) (c z) =
      DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun A (Fin r)) (fun j => w (σ j)) (w e) (w z) k := by
  let χ := balancedConfigurationChartEvaluation (R := R) i w a ha hw
  let ev : MvPolynomial (Fin m × Fin r) R →ₐ[R] A := MvPolynomial.aeval (fun jk : Fin m × Fin r => w jk.1 jk.2)
  let Q := FrameCoordinatePolynomials.balancedFrameCoordinateNumerator R σ e z (c z) k a (C z) ha (hC z)
  let P := MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) a
  have he : χ (FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC z k) * P = ev Q.val := by
    have h := Homogeneous.AwayEvaluation.homogeneousAwayEvaluation_mk_cross (DeterminantGrading.balancedDeterminantGrading R r m i)
      (FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha)
      (balancedConfigurationPolynomialEvaluation (R := R) w).toRingHom
      ((balancedConfigurationPolynomialEvaluation_denominator (R := R) w a ha).symm ▸ hw)
      (FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R a ha i) 1 Q
      (by simpa only [one_nsmul] using
        FrameCoordinatePolynomials.balancedFrameCoordinateNumerator_mem_grading R σ e z (c z) k a (C z) ha (hC z) i)
    simp only [pow_one] at h
    change χ (FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC z k) *
      balancedConfigurationPolynomialEvaluation (R := R) w (FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha) =
      ev Q.val at h
    rw [balancedConfigurationPolynomialEvaluation_denominator] at h
    exact h
  have hq := congrArg ev
    (FrameCoordinatePolynomials.balancedFrameCoordinateNumerator_crossMultiply R σ e z (c z) k a (C z) ha (hC z))
  have hev (b : (Fin r → Fin m) → ℕ) : ev (MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) b) =
      MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) b := by
    simp only [MonomialAlgebra.exponentMonomial, map_prod, map_pow, ev, LabeledDeterminantPolynomials.labeledDeterminantPolynomial_eval]
  change ev (Q.val * MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R)
      (Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z))) =
    ev (MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) a *
      MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) (Frame.CoordinateExponents.frameCoordinateExponent σ e z k)) at hq
  rw [map_mul, map_mul, hev (Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z)), hev a,
    hev (Frame.CoordinateExponents.frameCoordinateExponent σ e z k), Frame.CoordinateMonomials.frameCoordinateExponent_linearMap,
    Frame.CoordinateMonomials.frameCoordinateExponent_linearMap] at hq
  apply hw.mul_right_cancel
  calc
    _ = (χ (FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC z k) * P) *
        DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun A (Fin r)) (fun j => w (σ j)) (w e) (w z) (c z) := by ring
    _ = ev Q.val * DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun A (Fin r))
        (fun j => w (σ j)) (w e) (w z) (c z) := by rw [he]
    _ = P * DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun A (Fin r))
        (fun j => w (σ j)) (w e) (w z) k := hq
    _ = _ := mul_comm _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.ConfigurationChartEvaluation
