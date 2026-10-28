import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CompactHermitian
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OrthogonalHermitianCoordinates

/-! # Distinguished Hermitian -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.DistinguishedHermitian.IntrinsicHermitianMarking

noncomputable section

/-! The original Lie rank two gives actual Hermitian coordinates of
signature (2,1), after choosing the positive imaginary trace scalar. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (σ : E →ₐ[ℚ] ℂ) (hρ : ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)

theorem nativeHermitianMatrix_complex_symmetry
    (hconj : ComplexMultiplication.CM.TraceForm.cmFieldConjugation E ξ = -ξ) (i j : Fin 3) :
    σ (HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ i j) =
      star (σ (HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ j i)) :=
  (congrArg σ (HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix_symmetry A ρ s hs hg hdegree hρ ξ hconj i j)).trans
    (ComplexMultiplication.CM.TraceForm.cmFieldConjugation_embedding E σ _)

include hξ in
theorem exists_nativeHermitian_signature_coordinates
    (hconj : ComplexMultiplication.CM.TraceForm.cmFieldConjugation E ξ = -ξ) (him : 0 < (σ ξ).im)
    (hr : LieRanks.HasLieRank A.abelian ρ (σ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) 2) :
    ∃ e : (Fin 3 → ℂ) ≃ₗ[ℂ] ((Fin 2 → ℂ) × (Fin 1 → ℂ)), ∀ x y,
      Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom
        (HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) x y =
          (∑ i, (e x).1 i * star ((e y).1 i)) - ∑ j, (e x).2 j * star ((e y).2 j) := by
  let H := HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ
  let F := ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (H.map σ)
  have hF (x y : Fin 3 → ℂ) : F x y =
      Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom H x y :=
    ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm_apply (H.map σ) x y
  have hsym (x y : Fin 3 → ℂ) : F y x = star (F x y) :=
    ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm_symmetry (H.map σ)
      (nativeHermitianMatrix_complex_symmetry A ρ s hs hg hdegree σ hρ ξ hconj) x y
  let P := EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart A ρ s hs hg hdegree σ
  let Q := EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree σ
  have hweight (x y : Fin 3 → ℂ) :
      (EmbeddingSigns.IntrinsicHermitianMarking.weightedEmbeddingHermitian A ρ s hs hg hdegree hρ ξ σ x y).re = -(σ ξ).im * (F x y).re :=
    (ImaginaryHermitianWeights.imaginaryHermitianWeight_re (σ ξ) _ (ImaginaryHermitianWeights.imaginaryScalar_embedding_re σ ξ hconj)).trans
      (congrArg (fun z : ℂ => -(σ ξ).im * z.re) (hF x y).symm)
  have hc : -(σ ξ).im < 0 := neg_neg_of_pos him
  have hpos (x : P) (hx : x ≠ 0) : 0 < (F x.val x.val).re := by
    have hn : x.val ≠ 0 := fun h => hx (Subtype.ext h)
    have hw := EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart_negative A ρ s hs hg hdegree σ hρ ξ hξ x.val x.property hn
    rw [hweight] at hw
    exact ((mul_neg_iff.mp hw).resolve_left (fun h => (not_lt_of_ge hc.le) h.1)).2
  have hneg (x : Q) (hx : x ≠ 0) : (F x.val x.val).re < 0 := by
    have hn : x.val ≠ 0 := fun h => hx (Subtype.ext h)
    have hw := EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart_positive A ρ s hs hg hdegree σ hρ ξ hξ x.val x.property hn
    rw [hweight] at hw
    exact ((mul_pos_iff.mp hw).resolve_left (fun h => (not_lt_of_ge hc.le) h.1)).2
  have horth (x : P) (y : Q) : F x.val y.val = 0 := by
    have hw := EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianParts_orthogonal A ρ s hs hg hdegree σ hρ ξ hξ y.val x.val y.property x.property
    have hn : Complex.I * σ ξ ≠ 0 := mul_ne_zero Complex.I_ne_zero ((map_ne_zero σ).mpr hξ)
    have hf : F y.val x.val = 0 := (hF y.val x.val).trans ((mul_eq_zero.mp hw).resolve_left hn)
    exact (hsym y.val x.val).trans ((congrArg star hf).trans (map_zero (starRingEnd ℂ)))
  obtain ⟨e, he⟩ := OrthogonalHermitianCoordinates.exists_orthogonalHermitian_coordinates F hsym P Q
    (EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianParts_isCompl A ρ s hs hg hdegree σ).symm horth hpos hneg 2 1
    (EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart_finrank A ρ s hs hg hdegree σ hr)
    (EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart_finrank A ρ s hs hg hdegree σ hr)
  exact ⟨e, fun x y => (hF x y).symm.trans (he x y)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.DistinguishedHermitian.IntrinsicHermitianMarking
