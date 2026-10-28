import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum
import OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticBasis

/-! # Multiplicity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity

noncomputable section

/-! Insert the signed multiplicity line into the actual reference PEL
Hermitian form. Its trace coefficient and rational symplectic coordinates
are constructed from the native imaginary scalar and diagonal matrix. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization
open scoped Classical _root_.Matrix

section

/-- Match the place-index equality used in RadialDilation's exported Weil interface. -/
abbrev nativePlaceDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
abbrev nativeTripleDecidableEq : DecidableEq (Fin 3) := inferInstance

end

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

/-- The native period convention uses a negative imaginary coefficient at
the active negative line. The minus sign fixes that orientation. -/
def nativeCoefficient (v : Multiplicity.Odd.Sign E) : E := -Multiplicity.Odd.imaginaryCoefficient E v / P.imaginaryScalar

theorem nativeCoefficient_real (hP : P.IsAdmissible) (v : Multiplicity.Odd.Sign E) :
    ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (nativeCoefficient E P v) = nativeCoefficient E P v := by
  obtain ⟨_, _, _, _, _, _, _, hδ, _⟩ := hP
  change ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (-Multiplicity.Odd.imaginaryCoefficient E v / P.imaginaryScalar) = _
  rw [map_div₀, map_neg, Multiplicity.Odd.imaginaryCoefficient_conjugate]
  change - -Multiplicity.Odd.imaginaryCoefficient E v / NumberField.IsCMField.complexConj E P.imaginaryScalar = _
  rw [hδ, neg_div, div_neg, neg_neg]
  rfl

theorem nativeCoefficient_ne_zero (hP : P.IsAdmissible) (v : Multiplicity.Odd.Sign E) :
    nativeCoefficient E P v ≠ 0 := by
  obtain ⟨_, _, _, _, _, _, hδ, _⟩ := hP
  exact div_ne_zero (neg_ne_zero.mpr (Multiplicity.Odd.imaginaryCoefficient_ne_zero E v)) hδ

theorem native_orientedCoefficient (hP : P.IsAdmissible) (v : Multiplicity.Odd.Sign E) :
    P.imaginaryScalar * nativeCoefficient E P v = -Multiplicity.Odd.imaginaryCoefficient E v := by
  obtain ⟨_, _, _, _, _, _, hδ, _⟩ := hP
  exact mul_div_cancel₀ _ hδ

def nativePairing (v : Multiplicity.Odd.Sign E) (x y : E) : E :=
  nativeCoefficient E P v * x * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E y

theorem nativePairing_hermitian (hP : P.IsAdmissible) (v : Multiplicity.Odd.Sign E) (x y : E) :
    ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (nativePairing E P v x y) = nativePairing E P v y x := by
  simp only [nativePairing, map_mul, nativeCoefficient_real E P hP,
    ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply]
  ring

theorem nativePairing_nondegenerate (hP : P.IsAdmissible) (v : Multiplicity.Odd.Sign E) (x : E)
    (hx : ∀ y, nativePairing E P v x y = 0) : x = 0 := by
  have h := hx 1
  simp only [nativePairing, map_one, mul_one] at h
  exact (mul_eq_zero.mp h).resolve_left (nativeCoefficient_ne_zero E P hP v)

def nativeTensorPairing (v : Multiplicity.Odd.Sign E) (x y : Fin 3 → E) : E :=
  nativeCoefficient E P v * NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b x y

def nativeMatrix : Matrix (Fin 3) (Fin 3) E := Matrix.diagonal ![1, 1, P.b]

theorem nativeMatrix_hermitian (hP : P.IsAdmissible) :
    ∀ i j, nativeMatrix E P i j = NumberField.IsCMField.complexConj E (nativeMatrix E P j i) := by
  obtain ⟨_, hb, _⟩ := hP
  intro i j
  fin_cases i <;> fin_cases j <;> simp [nativeMatrix, Matrix.diagonal, hb]

omit [IsGalois ℚ E] in
theorem nativeMatrix_det_ne_zero (hP : P.IsAdmissible) : (nativeMatrix E P).det ≠ 0 := by
  obtain ⟨_, _, hb, _⟩ := hP
  simpa [nativeMatrix, Matrix.det_diagonal, Fin.prod_univ_succ] using hb

theorem native_tensor_trace (v : Multiplicity.Odd.Sign E) (x y : Fin 3 → E) :
    RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm E (P.imaginaryScalar * nativeCoefficient E P v) (nativeMatrix E P) x y =
      Algebra.trace ℚ E (P.imaginaryScalar * nativeTensorPairing E P v x y) := by
  rw [RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm_apply]
  congr 1
  simp [nativeMatrix, nativeTensorPairing, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian,
    Fin.sum_univ_succ, Matrix.diagonal]
  ring

theorem native_symplectic_coordinates (hP : P.IsAdmissible) (v : Multiplicity.Odd.Sign E) :
    ∃ e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ),
      ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
        Algebra.trace ℚ E (P.imaginaryScalar * nativeTensorPairing E P v x y) := by
  have hP' := hP
  obtain ⟨_, _, _, _, _, _, hδ0, hδ, _⟩ := hP'
  obtain ⟨e, he⟩ := RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.exists_rational_symplectic_coordinates E P.embeddings hP.1
    P.imaginaryScalar (nativeCoefficient E P v) hδ (nativeCoefficient_real E P hP v)
    (mul_ne_zero hδ0 (nativeCoefficient_ne_zero E P hP v))
    (nativeMatrix E P) (nativeMatrix_hermitian E P hP) (nativeMatrix_det_ne_zero E P hP)
  refine ⟨e, fun x y => (he x y).trans (native_tensor_trace E P v x y)⟩

theorem native_multiplicity_sign (hP : P.IsAdmissible) (v : Multiplicity.Odd.Sign E) (τ : Gal(E/ℚ)) :
    (if ((τ (P.imaginaryScalar * nativeCoefficient E P v) : E) : ℂ).im < 0 then (1 : ℤ) else -1) =
      ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹) := by
  rw [native_orientedCoefficient E P hP v]
  simp only [map_neg, IntermediateField.coe_neg, Complex.neg_im, neg_lt_zero]
  cases h : v.val τ⁻¹
  · rw [ite_eq_right (not_lt_of_ge (Multiplicity.Odd.imaginaryCoefficient_negative E v τ h).le)]
    rfl
  · rw [ite_eq_left (Multiplicity.Odd.imaginaryCoefficient_positive E v τ h)]
    rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity
