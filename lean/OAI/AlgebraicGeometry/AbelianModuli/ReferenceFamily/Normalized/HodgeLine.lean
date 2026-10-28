import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianNormalizer
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine

/-! # Hodge Line -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine

noncomputable section

/-! The constructed distinguished normalizer sends the actual native
Hodge line to a unique point of the prescribed negative-line ball. -/

theorem complexMatrixHermitian_diagonal {E : Type} [Field E]
    (σ : E →+* ℂ) (b : E) (x y : Fin 3 → ℂ) :
    Datum.RankThreePELDatum.complexMatrixHermitian σ (Matrix.diagonal ![1, 1, b]) x y =
      ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, σ b]) x y := by
  rw [OrthogonalHermitianCoordinates.complexHermitianMatrixForm_diagonal]
  simp [Datum.RankThreePELDatum.complexMatrixHermitian, Fin.sum_univ_succ, Matrix.diagonal]
  ring

namespace NativeHermitianMarking

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (σ : E →ₐ[ℚ] ℂ) (e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ))

def nativeNormalizedHodgeLine : Submodule ℂ (Fin 3 → ℂ) :=
  (Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree σ).map e.symm.toLinearMap

omit [NumberField.IsCMField E] in
theorem nativeNormalizedHodgeLine_finrank
    (hr : LieRanks.HasLieRank A.abelian ρ (σ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) 2) :
    Module.finrank ℂ (nativeNormalizedHodgeLine A ρ s hs hg hdegree σ e) = 1 :=
  (e.symm.finrank_map_eq _).trans (Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart_finrank A ρ s hs hg hdegree σ hr)

variable (hρ : ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)
    (hconj : ComplexMultiplication.CM.TraceForm.cmFieldConjugation E ξ = -ξ) (him : 0 < (σ ξ).im) (b : E)
    (he : ∀ x y, Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom
      (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) (e x) (e y) =
        Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom (Matrix.diagonal ![1, 1, b]) x y)

include hξ hconj him he in
theorem nativeNormalizedHodgeLine_negative (x : Fin 3 → ℂ)
    (hx : x ∈ nativeNormalizedHodgeLine A ρ s hs hg hdegree σ e) (hne : x ≠ 0) :
    (ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, σ b]) x x).re < 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hny : y ≠ 0 := fun hz => hne ((congrArg e.symm hz).trans e.symm.map_zero)
  have hw := Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart_positive A ρ s hs hg hdegree σ hρ ξ hξ y hy hny
  have hweight := ImaginaryHermitianWeights.imaginaryHermitianWeight_re (σ ξ)
    (Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom
      (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) y y)
    (ImaginaryHermitianWeights.imaginaryScalar_embedding_re σ ξ hconj)
  have hw' := (congrArg (fun r : ℝ => 0 < r) hweight).mp hw
  have hc : -(σ ξ).im < 0 := neg_neg_of_pos him
  have hnegative := ((mul_pos_iff.mp hw').resolve_left (fun h => (not_lt_of_ge hc.le) h.1)).2
  have hh := he (e.symm y) (e.symm y)
  rw [e.apply_symm_apply, complexMatrixHermitian_diagonal] at hh
  exact (congrArg Complex.re hh) ▸ hnegative

include hξ hconj him he in
theorem exists_unique_nativeHodge_ball_coordinate
    (hr : LieRanks.HasLieRank A.abelian ρ (σ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) 2) :
    ∃! z : Geometry.ComplexBall.PrescribedSignsB.BallChart,
      nativeNormalizedHodgeLine A ρ s hs hg hdegree σ e = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z} ∧
      (ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, σ b]) (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.lineVector z)).re < 0 :=
  NegativeLine.exists_unique_negativeLine_coordinate (σ b) (nativeNormalizedHodgeLine A ρ s hs hg hdegree σ e)
    (nativeNormalizedHodgeLine_finrank A ρ s hs hg hdegree σ e hr)
    (nativeNormalizedHodgeLine_negative A ρ s hs hg hdegree σ e hρ ξ hξ hconj him b he)

end NativeHermitianMarking

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine
