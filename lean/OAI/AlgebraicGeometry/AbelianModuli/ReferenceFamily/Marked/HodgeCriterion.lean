import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.ComplexTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion

/-! # Hodge Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.HodgeCriterion.IntrinsicHermitianMarking

noncomputable section

/-! Preservation of the actual marked Hodge subspaces at all field
embeddings proves the Hodge condition on the original rational periods. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)

omit [NumberField.IsCMField E] in
theorem markedPeriodTransport_isHodgeMap_of_parts
    (hu : ∀ (τ : E →ₐ[ℚ] ℂ) (x : Fin 3 → ℂ),
      x ∈ Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree τ →
        ((LinearMap.toMatrix' u.toLinearMap).map τ).mulVec x ∈
          Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart B σ s hs hg hdegree τ) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)))
      (PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A.abelian B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
        (Polarized.Projectivity.polarizedNativeProjectivePresentation B) ρ σ s hs hg hdegree u).toLinearMap := by
  let PA := Polarized.Projectivity.polarizedNativeProjectivePresentation A
  let PB := Polarized.Projectivity.polarizedNativeProjectivePresentation B
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian PA ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian PA ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.abelian PB σ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower B.abelian PB σ
  let HA := IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian PA)
  let HB := IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian PB)
  have hact (a : E) : ComplexMultiplication.WeightOne.CM.IsHodgeMap HA HA
      (ComplexMultiplication.WeightOne.CM.scalarEndomorphism (U := Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian PA)) E a) :=
    Complex.PeriodFieldAction.IntrinsicNumberFieldAction.fieldAction_isHodgeMap A.abelian PA ρ a
  apply EmbeddingHodgeCriterion.isHodgeMap_of_embedding_intersections E (Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A.abelian PA ρ s hs hg hdegree) HA hact HB
  intro τ v hv hh
  have hpos : Intrinsic.EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree v τ ∈
      Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree τ :=
    ⟨⟨v, hv⟩, hh, rfl⟩
  obtain ⟨y, hy, hey⟩ := hu τ _ hpos
  let tv : EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace B.abelian PB σ τ :=
    ⟨ComplexTransport.IntrinsicHermitianMarking.markedComplexTransport A B ρ σ s hs hg hdegree u v,
      ComplexTransport.IntrinsicHermitianMarking.markedComplexTransport_embedding A B ρ σ s hs hg hdegree u τ v hv⟩
  have ht : Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeEmbeddingCoordinateEquiv B σ s hs hg hdegree τ tv =
      Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeEmbeddingCoordinateEquiv B σ s hs hg hdegree τ y :=
    (ComplexTransport.IntrinsicHermitianMarking.markedComplexTransport_coordinates A B ρ σ s hs hg hdegree u v τ).trans hey.symm
  have hval := congrArg Subtype.val ((Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeEmbeddingCoordinateEquiv B σ s hs hg hdegree τ).injective ht)
  change tv.val ∈ (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian PB)).ker
  have hy' : y.val ∈ (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian PB)).ker := hy
  exact (congrArg (fun x => x ∈ (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian PB)).ker) hval).mpr hy'

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.HodgeCriterion.IntrinsicHermitianMarking
