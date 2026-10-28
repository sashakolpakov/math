import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Complement
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.IsometryEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns

/-! # Hermitian Complement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianComplement.IntrinsicHermitianMarking

noncomputable section

/-! Preservation of a marked positive Hodge summand by a Hermitian
isometry forces preservation of its actual negative complement. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hρ : ActionData.RosatiConjugation A ρ) (ξ : E) (τ : E →ₐ[ℚ] ℂ)

def weightedEmbeddingForm : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) →ₗ⋆[ℂ] ℂ :=
  (Complex.I * τ ξ) • ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm
    ((HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ).map τ)

theorem weightedEmbeddingForm_apply (x y : Fin 3 → ℂ) :
    weightedEmbeddingForm A ρ s hs hg hdegree hρ ξ τ x y =
      EmbeddingSigns.IntrinsicHermitianMarking.weightedEmbeddingHermitian A ρ s hs hg hdegree hρ ξ τ x y := by
  change (Complex.I * τ ξ) * ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm
    ((HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ).map τ) x y = _
  rw [ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm_apply]
  rfl

variable (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
    (hσ : ActionData.RosatiConjugation B σ)

theorem markedHermitian_isometry_preserves_negative
    (hξ : ξ ≠ 0) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hu : ∀ x y, Datum.RankThreePELDatum.matrixHermitian (HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix B σ s hs hg hdegree hσ ξ) (u x) (u y) =
      Datum.RankThreePELDatum.matrixHermitian (HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) x y)
    (hP : ∀ p' ∈ EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart B σ s hs hg hdegree τ,
      ∃ p ∈ EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree τ,
        ((LinearMap.toMatrix' u).map τ).mulVec p = p')
    (q : Fin 3 → ℂ) (hq : q ∈ EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart A ρ s hs hg hdegree τ) :
    ((LinearMap.toMatrix' u).map τ).mulVec q ∈ EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart B σ s hs hg hdegree τ := by
  let F := weightedEmbeddingForm A ρ s hs hg hdegree hρ ξ τ
  let G := weightedEmbeddingForm B σ s hs hg hdegree hσ ξ τ
  let m := Matrix.toLin' ((LinearMap.toMatrix' u).map τ)
  apply Hermitian.Complement.hermitianMap_complement F G
    (EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree τ)
    (EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart A ρ s hs hg hdegree τ)
    (EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart B σ s hs hg hdegree τ)
    (EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart B σ s hs hg hdegree τ)
    (EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianParts_isCompl B σ s hs hg hdegree τ)
    ?_ ?_ ?_ m ?_ hP q hq
  · intro p hp hn
    rw [weightedEmbeddingForm_apply]
    exact EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart_positive B σ s hs hg hdegree τ hσ ξ hξ p hp hn
  · intro p hp r hr
    rw [weightedEmbeddingForm_apply]
    exact EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianParts_orthogonal A ρ s hs hg hdegree τ hρ ξ hξ p r hp hr
  · intro p hp r hr
    rw [weightedEmbeddingForm_apply]
    exact EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianParts_orthogonal B σ s hs hg hdegree τ hσ ξ hξ p r hp hr
  · intro x y
    change (Complex.I * τ ξ) * ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm
      ((HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix B σ s hs hg hdegree hσ ξ).map τ) (m x) (m y) =
        (Complex.I * τ ξ) * ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm
          ((HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ).map τ) x y
    exact congrArg (fun z : ℂ => (Complex.I * τ ξ) * z)
      (Hermitian.IsometryEmbedding.hermitianIsometry_embedding _ _ u hu τ x y)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianComplement.IntrinsicHermitianMarking
