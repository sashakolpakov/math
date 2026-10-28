import OAI.AlgebraicGeometry.PELModuli.CMPoints.HermitianDiagonalization
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ZeroPeriod
import OAI.NumberTheory.ArithmeticGroups.Diagonal

/-! # Rational Ball Point -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.RationalBallPoint

noncomputable section

/-! A rational negative vector gives an actual point of the specified
ball chart, even when the component uses a different Hermitian matrix. -/

open scoped Classical

open _root_.Module

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

omit [NumberField E] [NumberField.IsCMField E] in
theorem negative_vector_last_ne_zero (w : Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hw : (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) w w).re < 0) :
    w 2 ≠ 0 := by
  change (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b])
    P.distinguished w (star w)).re < 0 at hw
  rw [NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal_real] at hw
  intro hz
  simp only [hz, map_zero, mul_zero, add_zero] at hw
  exact (not_lt_of_ge (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))) hw

def normalizedBallChart (w : Geometry.ComplexBall.PrescribedSignsB.Vec) : Geometry.ComplexBall.PrescribedSignsB.BallChart := fun i => w i.castSucc / w 2

omit [NumberField E] [NumberField.IsCMField E] in
theorem normalizedBallChart_mem_domain (w : Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hw : (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) w w).re < 0) :
    normalizedBallChart w ∈ P.domain := by
  have hz := negative_vector_last_ne_zero P w hw
  have hp : 0 < Complex.normSq (w 2) := Complex.normSq_pos.mpr hz
  change (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b])
    P.distinguished w (star w)).re < 0 at hw
  rw [NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal_real] at hw
  change (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b])
    P.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector _) (star (Geometry.ComplexBall.PrescribedSignsB.lineVector _))).re < 0
  rw [NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal_real]
  change Complex.normSq (w 0 / w 2) + Complex.normSq (w 1 / w 2) +
    (P.embeddings P.distinguished P.b).re * Complex.normSq (1 : ℂ) < 0
  simp only [map_div₀, map_one, mul_one]
  have heq : Complex.normSq (w 0) / Complex.normSq (w 2) +
      Complex.normSq (w 1) / Complex.normSq (w 2) + (P.embeddings P.distinguished P.b).re =
      (Complex.normSq (w 0) + Complex.normSq (w 1) +
        (P.embeddings P.distinguished P.b).re * Complex.normSq (w 2)) / Complex.normSq (w 2) := by
    field_simp
  rw [heq]
  exact div_neg_of_neg_of_pos hw hp

theorem lineVector_normalizedBallChart (w : Geometry.ComplexBall.PrescribedSignsB.Vec) (hw : w 2 ≠ 0) :
    Geometry.ComplexBall.PrescribedSignsB.lineVector (normalizedBallChart w) = (w 2)⁻¹ • w := by
  ext i
  fin_cases i <;> simp [Geometry.ComplexBall.PrescribedSignsB.lineVector, normalizedBallChart, hw, div_eq_mul_inv, mul_comm]

theorem exists_rational_ball_line (hP : P.IsAdmissible)
    (H : Matrix (Fin 3) (Fin 3) E) (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (he : ∀ x y, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y) :
    ∃ (z : P.Domain) (v : Fin 3 → E) (a : ℂ),
      v ≠ 0 ∧ a ≠ 0 ∧
      e (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val) = a • (fun i => P.μ (v i)) ∧
      (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (fun i => P.μ (v i))
        (fun i => P.μ (v i))).re < 0 := by
  have hzero : (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H
      (e (Geometry.ComplexBall.PrescribedSignsB.lineVector 0)) (e (Geometry.ComplexBall.PrescribedSignsB.lineVector 0))).re < 0 := by
    rw [he]
    exact ZeroPeriod.zero_mem_period_domain P hP
  obtain ⟨v, hv0, hv⟩ := RationalNegativeLine.exists_rational_negative_vector
    (P.embeddings P.distinguished) H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector 0)) hzero
  let w : Geometry.ComplexBall.PrescribedSignsB.Vec := e.symm (fun i => P.μ (v i))
  have hw : (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) w w).re < 0 := by
    rw [← he, LinearEquiv.apply_symm_apply]
    exact hv
  have hw2 := negative_vector_last_ne_zero P w hw
  refine ⟨⟨normalizedBallChart w, normalizedBallChart_mem_domain P w hw⟩,
    v, (w 2)⁻¹, hv0, inv_ne_zero hw2, ?_, hv⟩
  rw [lineVector_normalizedBallChart w hw2, map_smul]
  exact congrArg ((w 2)⁻¹ • ·) (e.apply_symm_apply _)

theorem exists_rational_ball_orthogonal_basis (hP : P.IsAdmissible)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i))
    (hani : ∀ x : Fin 3 → E, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H x x = 0 → x = 0)
    (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (he : ∀ x y, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y) :
    ∃ (z : P.Domain) (b : Basis (Fin 3) E (Fin 3 → E)) (a : ℂ),
      a ≠ 0 ∧ e (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val) = a • (fun i => P.μ (b 0 i)) ∧
      Pairwise (fun i j => AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b i) (b j) = 0) := by
  obtain ⟨z, v, a, hv, ha, heq, _⟩ := exists_rational_ball_line P hP H e he
  obtain ⟨b, hb, ho⟩ := HermitianDiagonalization.exists_anisotropic_orthogonal_basis_with_first
    (HermitianDiagonalization.matrixHermitianFirstLinear H)
    (HermitianDiagonalization.matrixHermitian_orthogonal_symm H hH) hani v hv 2 (by simp)
  exact ⟨z, b, a, ha, by simpa [hb] using heq, ho⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.RationalBallPoint
