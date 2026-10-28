import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingTracePairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingHodgeRanks
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking

/-! # Embedding Chern Matrix -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingChernMatrix.IntrinsicHermitianMarking

noncomputable section

/-! The actual marked Hermitian matrix recovers the original Chern
pairing separately on each genuine embedding block. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingHodgeRanks.IntrinsicNumberFieldAction

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

def nativeMarkedComplexCoordinates :
    ComplexMultiplication.WeightOne.CM.Complexification (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))) ≃ₗ[ℂ]
      ((E →ₐ[ℚ] ℂ) → Fin 3 → ℂ) := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  exact RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates E
    (PELMarking.IntrinsicPELMarking.coordinates A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ s hs hg hdegree)

theorem nativePolarization_complexMatrix (hρ : ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)
    (u v : ComplexMultiplication.WeightOne.CM.Complexification (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)))) :
    LinearMap.BilinForm.baseChange ℂ (ChernPairing.nativePolarizationForm A) u
      (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))) v) =
      ∑ σ : E →ₐ[ℚ] ℂ, σ ξ * ∑ i, ∑ j,
        nativeMarkedComplexCoordinates A ρ s hs hg hdegree u σ i *
          σ (HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ i j) *
            star (nativeMarkedComplexCoordinates A ρ s hs hg hdegree v σ j) := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let e := PELMarking.IntrinsicPELMarking.coordinates A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ s hs hg hdegree
  apply EmbeddingTracePairing.rankThree_trace_conjugate e (ChernPairing.nativePolarizationForm A) _ ξ
  intro x y
  have ht := HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix_trace A ρ s hs hg hdegree hρ ξ hξ (e x) (e y)
  have he : HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm A ρ s hs hg hdegree (e x) (e y) = ChernPairing.nativePolarizationForm A x y := by
    change ChernPairing.nativePolarizationForm A (e.symm (e x)) (e.symm (e y)) = _
    rw [e.symm_apply_apply, e.symm_apply_apply]
  exact he.symm.trans ht.symm

theorem nativePolarization_embeddingMatrix (hρ : ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)
    (σ : E →ₐ[ℚ] ℂ)
    (u v : ComplexMultiplication.WeightOne.CM.Complexification (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))))
    (hu : u ∈ EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ σ) :
    LinearMap.BilinForm.baseChange ℂ (ChernPairing.nativePolarizationForm A) u
      (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))) v) =
      σ ξ * ∑ i, ∑ j,
        nativeMarkedComplexCoordinates A ρ s hs hg hdegree u σ i *
          σ (HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ i j) *
            star (nativeMarkedComplexCoordinates A ρ s hs hg hdegree v σ j) := by
  classical
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let e := PELMarking.IntrinsicPELMarking.coordinates A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ s hs hg hdegree
  rw [nativePolarization_complexMatrix A ρ s hs hg hdegree hρ ξ hξ]
  apply Finset.sum_eq_single σ
  · intro τ _ hτ
    have hz (i : Fin 3) : nativeMarkedComplexCoordinates A ρ s hs hg hdegree u τ i = 0 :=
      RankThreeEmbeddingCoordinates.rankThreeEmbedding_coordinate_zero E e σ τ hτ hu i
    simp only [hz, zero_mul, Finset.sum_const_zero, mul_zero]
  · intro hn
    exact (hn (Finset.mem_univ σ)).elim

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingChernMatrix.IntrinsicHermitianMarking
