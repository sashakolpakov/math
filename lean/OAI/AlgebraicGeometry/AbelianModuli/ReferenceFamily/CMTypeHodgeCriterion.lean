import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianComplement
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingConjugation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.HodgeCriterion

/-! # CM Type Hodge Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMTypeHodgeCriterion

noncomputable section

/-! The Hodge condition for a marked Hermitian isometry can be checked
on one embedding from each conjugate pair. Orthogonality and coefficient
conjugation determine the other half. -/

theorem star_embeddedMatrix_conjugate {E : Type} [Field E] [Algebra ℚ E]
    (m : Matrix (Fin 3) (Fin 3) E) (τ : E →ₐ[ℚ] ℂ) (x : Fin 3 → ℂ) :
    star ((m.map (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ)).mulVec x) = (m.map τ).mulVec (star x) := by
  funext i
  simp [Matrix.mulVec, dotProduct, ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_apply]

namespace NativeHermitianMarking

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hρ : ActionData.RosatiConjugation A ρ) (hσ : ActionData.RosatiConjugation B σ)
    (ξ : E) (hξ : ξ ≠ 0) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)

include hξ in
theorem markedPeriodTransport_isHodgeMap_of_CMType
    (τ : Fin s → E →ₐ[ℚ] ℂ)
    (hτ : Function.Surjective (fun p : Fin s × Bool => if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (τ p.1) else τ p.1))
    (hu : ∀ x y, Datum.RankThreePELDatum.matrixHermitian (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix B σ s hs hg hdegree hσ ξ) (u x) (u y) =
      Datum.RankThreePELDatum.matrixHermitian (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) x y)
    (hP : ∀ i, (Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree (τ i)).map
      (Matrix.toLin' ((LinearMap.toMatrix' u.toLinearMap).map (τ i))) =
        Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart B σ s hs hg hdegree (τ i)) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)))
      (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A.abelian B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
        (Polarized.Projectivity.polarizedNativeProjectivePresentation B) ρ σ s hs hg hdegree u).toLinearMap := by
  apply Marked.HodgeCriterion.IntrinsicHermitianMarking.markedPeriodTransport_isHodgeMap_of_parts A B ρ σ s hs hg hdegree u
  intro κ x hx
  obtain ⟨⟨i, b⟩, rfl⟩ := hτ κ
  cases b with
  | false =>
    exact (hP i) ▸ (show ((LinearMap.toMatrix' u.toLinearMap).map (τ i)).mulVec x ∈
      (Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree (τ i)).map
        (Matrix.toLin' ((LinearMap.toMatrix' u.toLinearMap).map (τ i))) from ⟨x, hx, rfl⟩)
  | true =>
    apply (Intrinsic.EmbeddingConjugation.IntrinsicHermitianMarking.nativePositivePart_conjugate_iff B σ s hs hg hdegree (τ i) _).mpr
    change star (((LinearMap.toMatrix' u.toLinearMap).map (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (τ i))).mulVec x) ∈
      Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart B σ s hs hg hdegree (τ i)
    rw [star_embeddedMatrix_conjugate]
    apply Intrinsic.HermitianComplement.IntrinsicHermitianMarking.markedHermitian_isometry_preserves_negative A ρ s hs hg hdegree hρ ξ (τ i) B σ hσ hξ u.toLinearMap hu
    · intro p hp
      have hp' : p ∈ (Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree (τ i)).map
          (Matrix.toLin' ((LinearMap.toMatrix' u.toLinearMap).map (τ i))) := (hP i).symm ▸ hp
      exact hp'
    · exact (Intrinsic.EmbeddingConjugation.IntrinsicHermitianMarking.nativePositivePart_conjugate_iff A ρ s hs hg hdegree (τ i) x).mp hx

end NativeHermitianMarking

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMTypeHodgeCriterion
