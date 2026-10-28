import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.DistinguishedHermitian
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OrthogonalHermitianCoordinates

/-! # Hermitian Normalizer -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianNormalizer.IntrinsicHermitianMarking

noncomputable section

/-! Normalize the reconstructed polarization matrix to the prescribed
distinguished diagonal form through a constructed linear equivalence. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (σ : E →ₐ[ℚ] ℂ) (hρ : ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)

include hξ in
theorem exists_nativeHermitian_normalizer
    (hconj : ComplexMultiplication.CM.TraceForm.cmFieldConjugation E ξ = -ξ) (him : 0 < (σ ξ).im)
    (hr : LieRanks.HasLieRank A.abelian ρ (σ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) 2)
    (b : E) (hb : ComplexMultiplication.CM.TraceForm.cmFieldConjugation E b = b) (hbneg : (σ b).re < 0) :
    ∃ e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ), ∀ x y,
      Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom
        (HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) (e x) (e y) =
          Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom (Matrix.diagonal ![1, 1, b]) x y := by
  let H := HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ
  let F := ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (H.map σ)
  have hF (x y : Fin 3 → ℂ) : F x y =
      Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom H x y :=
    ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm_apply (H.map σ) x y
  obtain ⟨d, hd⟩ := DistinguishedHermitian.IntrinsicHermitianMarking.exists_nativeHermitian_signature_coordinates A ρ s hs hg hdegree σ hρ ξ hξ hconj him hr
  have hreal : (σ b).im = 0 := by
    have hc := (ComplexMultiplication.CM.TraceForm.cmFieldConjugation_embedding E σ b).symm.trans (congrArg σ hb)
    have hi := congrArg Complex.im hc
    simp only [Complex.star_def, Complex.conj_im] at hi
    linarith
  obtain ⟨e, he⟩ := OrthogonalHermitianCoordinates.exists_prescribedDiagonal_normalizer F d
    (fun x y => (hF x y).trans (hd x y)) (σ b) hreal hbneg
  refine ⟨e, fun x y => (hF (e x) (e y)).symm.trans ((he x y).trans ?_)⟩
  have hm : (Matrix.diagonal ![1, 1, b]).map σ = Matrix.diagonal ![1, 1, σ b] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  exact (congrArg (fun M => ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm M x y) hm).symm.trans
    (ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm_apply ((Matrix.diagonal ![1, 1, b]).map σ) x y)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianNormalizer.IntrinsicHermitianMarking
