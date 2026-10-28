import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity
import OAI.NumberTheory.ArithmeticGroups.Diagonal

/-! # Period -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Period

noncomputable section

/-! The native signed trace form has the prescribed positive period frame.
The imaginary coefficient's orientation is fixed by the active negative line. -/

open scoped Classical _root_.Matrix

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

def nativeArchLabel (i : Fin s) : Gal(E/ℚ) := (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).symm (P.embeddings i)

omit [NumberField E] [NumberField.IsCMField E] in
theorem nativeArchLabel_spec (i : Fin s) (x : E) :
    ((nativeArchLabel E P i x : E) : ℂ) = P.embeddings i x :=
  congrArg (fun f : E →ₐ[ℚ] ℂ => f x) ((ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).apply_symm_apply (P.embeddings i))

omit [NumberField E] [NumberField.IsCMField E] in
theorem nativeArchLabel_active (hμ : P.μ = E.val.toRingHom) :
    nativeArchLabel E P P.distinguished = 1 := by
  apply (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).injective
  change ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E ((ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).symm _) = _
  rw [(ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).apply_symm_apply]
  ext x
  exact RingHom.congr_fun hμ x

def nativeCompactSigns (v : Odd.Sign E) (i : Fin s) : Bool := v.val (nativeArchLabel E P i)⁻¹

def nativeUpperFrame (hP : P.IsAdmissible) (v : Odd.Sign E)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) : Matrix (Fin s × Fin 3) (Fin s × Fin 3) ℂ :=
  RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.upperFrame (RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates E P.embeddings hP.1 e) (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Intrinsic.Multiplicity.nativeMatrix E P))
    P.distinguished (nativeCompactSigns E P v) z

def nativeLowerFrame (hP : P.IsAdmissible) (v : Odd.Sign E)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) : Matrix (Fin s × Fin 3) (Fin s × Fin 3) ℂ :=
  RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.lowerFrame (RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates E P.embeddings hP.1 e) (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Intrinsic.Multiplicity.nativeMatrix E P))
    P.distinguished (nativeCompactSigns E P v) z

theorem native_weight_value (hP : P.IsAdmissible) (v : Odd.Sign E) (i : Fin s) :
    P.embeddings i (P.imaginaryScalar * Intrinsic.Multiplicity.nativeCoefficient E P v) =
      -((nativeArchLabel E P i (Odd.imaginaryCoefficient E v) : E) : ℂ) := by
  rw [Intrinsic.Multiplicity.native_orientedCoefficient E P hP v, map_neg, nativeArchLabel_spec]

omit [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E] in
theorem native_frame_denominator (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Intrinsic.Multiplicity.nativeMatrix E P) P.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.axis 2) =
      P.embeddings P.distinguished P.b := by
  rw [Geometry.ComplexBall.PrescribedSignsB.matrixB_apply]
  change Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b]) P.distinguished _ _ = _
  rw [NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal]
  simp [Geometry.ComplexBall.PrescribedSignsB.lineVector, Geometry.ComplexBall.PrescribedSignsB.axis]

theorem native_frame_positive
    (hP : P.IsAdmissible) (hμ : P.μ = E.val.toRingHom)
    (v : Odd.Sign E) (hv : v.val 1 = true) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain) :
    ∀ i u, u ∈ LinearMap.range (Geometry.ComplexBall.PrescribedSignsB.placeFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Intrinsic.Multiplicity.nativeMatrix E P))
      P.distinguished (nativeCompactSigns E P v) z i) → u ≠ 0 →
      0 < (P.embeddings i (P.imaginaryScalar * Intrinsic.Multiplicity.nativeCoefficient E P v) *
        Geometry.ComplexBall.PrescribedSignsB.metricValue (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Intrinsic.Multiplicity.nativeMatrix E P) i) u / Complex.I).re := by
  let B := Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Intrinsic.Multiplicity.nativeMatrix E P)
  have hB := Geometry.ComplexBall.PrescribedSignsB.matrixB_hermitian P.embeddings (Intrinsic.Multiplicity.nativeMatrix E P) (Intrinsic.Multiplicity.nativeMatrix_hermitian E P hP)
  have hBapply (i : Fin s) (x y : Geometry.ComplexBall.PrescribedSignsB.Vec) : B i x y =
      Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b]) i x y :=
    Geometry.ComplexBall.PrescribedSignsB.matrixB_apply P.embeddings (Intrinsic.Multiplicity.nativeMatrix E P) i x y
  have hp : ∀ x : Geometry.ComplexBall.PrescribedSignsB.Vec, x ≠ 0 → x 2 = 0 → 0 < (B P.distinguished x (star x)).re := by
    intro x hx hx2
    rw [hBapply]
    exact NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.diagonal_positive_plane P.embeddings P.b P.distinguished x hx hx2
  have hc : ∀ i, i ≠ P.distinguished → Geometry.ComplexBall.PrescribedSignsB.PositiveB (B i) := by
    intro i hi x hx
    rw [hBapply]
    exact NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.diagonal_positive_definite P.embeddings P.b i (hP.2.2.2.2.1 i hi) x hx
  have hzB : (B P.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (star (Geometry.ComplexBall.PrescribedSignsB.lineVector z))).re < 0 := by
    rw [hBapply]
    exact hz
  have hq : B P.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.axis 2) ≠ 0 := by
    rw [show B P.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.axis 2) = P.embeddings P.distinguished P.b from
      native_frame_denominator E P z]
    exact (map_ne_zero _).mpr hP.2.2.1
  intro i u hu hne
  have ht : (P.embeddings i (P.imaginaryScalar * Intrinsic.Multiplicity.nativeCoefficient E P v)).re = 0 :=
    Geometry.ComplexBall.PrescribedSignsB.coefficient_real_zero (P.embeddings i) P.imaginaryScalar (Intrinsic.Multiplicity.nativeCoefficient E P v)
      hP.2.2.2.2.2.2.2.1 (Intrinsic.Multiplicity.nativeCoefficient_real E P hP v)
  apply Geometry.ComplexBall.PrescribedSignsB.wantedSign_positive B hB P.distinguished hp (fun i hi => Or.inl (hc i hi))
    (nativeCompactSigns E P v) z hzB hq i _ ht _ u hu hne
  rw [native_weight_value E P hP v i, Complex.neg_im]
  by_cases hi : i = P.distinguished
  · subst i
    simp only [Geometry.ComplexBall.PrescribedSignsB.wantedSign, Bool.false_eq_true, ↓reduceIte,
      nativeArchLabel_active E P hμ, AlgEquiv.one_apply]
    have h := Odd.imaginaryCoefficient_positive E v 1 (by simpa only [inv_one] using hv)
    exact neg_neg_of_pos h
  · simp only [Geometry.ComplexBall.PrescribedSignsB.wantedSign, ite_eq_right hi, decide_eq_true (hc i hi), Bool.not_true]
    cases hd : nativeCompactSigns E P v i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact neg_pos.mpr (Odd.imaginaryCoefficient_negative E v (nativeArchLabel E P i) hd)
    · simp only [↓reduceIte]
      exact neg_neg_of_pos (Odd.imaginaryCoefficient_positive E v (nativeArchLabel E P i) hd)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Period
