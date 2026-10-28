import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OneCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.NormalizedFrame

/-! # One Diagonal Normalizer -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneDiagonalNormalizer

noncomputable section

/-! The actual AdelicTheta orthonormal bases are explicit real diagonal scales.
These formulas retain the original native CM embeddings. -/

open scoped Classical _root_.NumberField Kronecker _root_.Matrix
open _root_.NumberField

namespace Quadratic

theorem complexDiagonalNormalizer_inv {I : Type*} [Fintype I] [DecidableEq I]
    (r : I → ℝ) (hr : ∀ i, r i ≠ 0) :
    (ThetaCycle.DiagonalNormalization.CM.complexDiagonalNormalizer r hr).inv =
      Matrix.diagonal (fun i => (Real.sqrt |r i| : ℂ)) := by
  simp [ThetaCycle.DiagonalNormalization.CM.complexDiagonalNormalizer, ThetaCycle.DiagonalFrame.CM.diagonalMatrixUnit, ThetaCycle.DiagonalNormalization.CM.diagonalNormalizationScale]

end Quadratic

namespace Multiplicity

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneDiagonalNormalizer.Quadratic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)

def nativeOneRadius (i : Fin s) : ℝ := Real.sqrt |(P.embeddings i P.b).re|

def nativeOneScale (i : Fin s) : ℝ :=
  Real.sqrt |2 * (P.embeddings i (P.imaginaryScalar * Intrinsic.Multiplicity.nativeCoefficient E P v)).im|

include hP hμ in
theorem nativeOneRadius_pos (i : Fin s) : 0 < nativeOneRadius E P i := by
  apply Real.sqrt_pos.mpr
  apply abs_pos.mpr
  have h := ThetaCycle.CMFormCoordinates.CM.source_hermitian_coefficients_ne_zero E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ)
    P.b hP.2.1 hP.2.2.1 i 2
  simpa [ThetaCycle.CMFormCoordinates.CM.sourceHermitianRealCoefficients, Intrinsic.IntrinsicOne.Multiplicity.nativePlaces_embeddings] using h

include hP hμ in
theorem nativeOneScale_pos (i : Fin s) : 0 < nativeOneScale E P v i := by
  apply Real.sqrt_pos.mpr
  apply abs_pos.mpr
  have h := Multiplicity.OneLocal.Quadratic.singleSkewRealCoefficient_ne_zero E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ)
    P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP) (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP)
    (Intrinsic.Multiplicity.nativeCoefficient E P v) (Intrinsic.Multiplicity.nativeCoefficient_real E P hP v)
    (Intrinsic.Multiplicity.nativeCoefficient_ne_zero E P hP v) i
  simpa only [Multiplicity.OneLocal.Quadratic.singleSkewRealCoefficient, Intrinsic.IntrinsicOne.Multiplicity.nativePlaces_embeddings] using h

theorem nativeOneBasisV_inv (i : Fin s) :
    ((Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).basisV i).inv =
      Matrix.diagonal ![(1 : ℂ), 1, (nativeOneRadius E P i : ℂ)] := by
  change (ThetaCycle.DiagonalNormalization.CM.complexDiagonalNormalizer
    (ThetaCycle.CMFormCoordinates.CM.sourceHermitianRealCoefficients E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ) P.b i)
    (ThetaCycle.CMFormCoordinates.CM.source_hermitian_coefficients_ne_zero E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ)
      P.b hP.2.1 hP.2.2.1 i)).inv = _
  rw [Quadratic.complexDiagonalNormalizer_inv]
  congr 1
  funext j
  fin_cases j <;>
    simp [ThetaCycle.CMFormCoordinates.CM.sourceHermitianRealCoefficients, nativeOneRadius, Intrinsic.IntrinsicOne.Multiplicity.nativePlaces_embeddings]

theorem nativeOneBasisP_inv (i : Fin s) :
    ((Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).basisP i).inv =
      Matrix.diagonal (fun _ : Fin 1 => (nativeOneScale E P v i : ℂ)) := by
  change (ThetaCycle.DiagonalNormalization.CM.complexDiagonalNormalizer
    (fun _ : Fin 1 => Multiplicity.OneLocal.Quadratic.singleSkewRealCoefficient E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ)
      P.imaginaryScalar (Intrinsic.Multiplicity.nativeCoefficient E P v) i)
    (fun _ => Multiplicity.OneLocal.Quadratic.singleSkewRealCoefficient_ne_zero E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ)
      P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP) (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP)
      (Intrinsic.Multiplicity.nativeCoefficient E P v) (Intrinsic.Multiplicity.nativeCoefficient_real E P hP v)
      (Intrinsic.Multiplicity.nativeCoefficient_ne_zero E P hP v) i)).inv = _
  rw [Quadratic.complexDiagonalNormalizer_inv]
  simp only [Multiplicity.OneLocal.Quadratic.singleSkewRealCoefficient, nativeOneScale, Intrinsic.IntrinsicOne.Multiplicity.nativePlaces_embeddings]

theorem nativeOneTensorNormalizer (i : Fin s) :
    ((Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).basisV i).inv ⊗ₖ
        ((Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).basisP i).inv =
      Matrix.diagonal (fun ij : Fin 3 × Fin 1 =>
        (![nativeOneScale E P v i, nativeOneScale E P v i,
          nativeOneScale E P v i * nativeOneRadius E P i] ij.1 : ℂ)) := by
  rw [nativeOneBasisV_inv, nativeOneBasisP_inv, Matrix.diagonal_kronecker_diagonal]
  congr 1
  funext ⟨j, k⟩
  fin_cases j <;> simp [mul_comm]

end Multiplicity

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneDiagonalNormalizer
