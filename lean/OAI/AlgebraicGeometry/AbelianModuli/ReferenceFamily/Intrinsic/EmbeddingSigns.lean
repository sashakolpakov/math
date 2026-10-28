import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingChernMatrix
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodPolarization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization

/-! # Embedding Signs -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking

noncomputable section

section

/-! The original Chern positivity determines the signs of each actual
Hermitian embedding block on its two native Hodge subspaces. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hρ : ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0) (σ : E →ₐ[ℚ] ℂ)

def weightedEmbeddingHermitian (u v : Fin 3 → ℂ) : ℂ :=
  Complex.I * σ ξ * Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom
    (HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) u v

include hξ in
theorem weightedEmbeddingHermitian_Chern
    (u v : ComplexMultiplication.WeightOne.CM.Complexification (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))))
    (hu : u ∈ EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ σ) :
    Complex.I * ReferenceFamily.Complex.PeriodRiemannPairing.complexChernForm (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))
      (ChernPairing.polarizationLineBundle A) u
      (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))) v) =
      weightedEmbeddingHermitian A ρ s hs hg hdegree hρ ξ σ
        (EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree u σ)
        (EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree v σ) := by
  have h := EmbeddingChernMatrix.IntrinsicHermitianMarking.nativePolarization_embeddingMatrix A ρ s hs hg hdegree hρ ξ hξ σ u v hu
  have hi := congrArg (fun z : ℂ => Complex.I * z) h
  exact hi.trans (mul_assoc Complex.I (σ ξ) _).symm

include hξ in
theorem weightedEmbeddingHermitian_holomorphic_positive
    (u : ComplexMultiplication.WeightOne.CM.Complexification (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))))
    (hu : u ∈ EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ σ)
    (hp : u ∈ (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))).ker)
    (hne : u ≠ 0) :
    0 < (weightedEmbeddingHermitian A ρ s hs hg hdegree hρ ξ σ
      (EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree u σ)
      (EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree u σ)).re := by
  have hpos := PeriodPolarization.complexChernForm_periodKernel_positive
    (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)) (ChernPairing.polarizationLineBundle A)
    (ChernPairing.polarizationLineBundle_ample A) u hp hne
  exact (congrArg Complex.re (weightedEmbeddingHermitian_Chern A ρ s hs hg hdegree hρ ξ hξ σ u u hu)) ▸ hpos

include hξ in
theorem weightedEmbeddingHermitian_antiholomorphic_negative
    (u : ComplexMultiplication.WeightOne.CM.Complexification (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))))
    (hu : u ∈ EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ σ)
    (hp : u ∈ IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.conjugatePeriodKernel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)))
    (hne : u ≠ 0) :
    (weightedEmbeddingHermitian A ρ s hs hg hdegree hρ ξ σ
      (EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree u σ)
      (EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree u σ)).re < 0 := by
  have hneg := PeriodPolarization.complexChernForm_conjugateKernel_negative
    (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)) (ChernPairing.polarizationLineBundle A)
    (ChernPairing.polarizationLineBundle_ample A) u hp hne
  exact (congrArg Complex.re (weightedEmbeddingHermitian_Chern A ρ s hs hg hdegree hρ ξ hξ σ u u hu)) ▸ hneg

end

/-! The weighted Hermitian embedding blocks have complementary
strictly positive and strictly negative subspaces in literal C cubed,
with dimensions computed from the original Lie ranks. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (σ : E →ₐ[ℚ] ℂ)

def nativeEmbeddingCoordinateEquiv :
    EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ σ ≃ₗ[ℂ] (Fin 3 → ℂ) := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  exact RankThreeEmbeddingCoordinates.rankThreeEmbeddingSpaceEquiv E
    (PELMarking.IntrinsicPELMarking.coordinates A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ s hs hg hdegree) σ

omit [NumberField.IsCMField E] in
theorem nativeEmbeddingCoordinateEquiv_apply
    (u : EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ σ) :
    nativeEmbeddingCoordinateEquiv A ρ s hs hg hdegree σ u =
      EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree u.val σ := rfl

def nativeHermitianPositivePart : Submodule ℂ (Fin 3 → ℂ) :=
  ((PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))).ker.comap
    (EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ σ).subtype).map
      (nativeEmbeddingCoordinateEquiv A ρ s hs hg hdegree σ).toLinearMap

def nativeHermitianNegativePart : Submodule ℂ (Fin 3 → ℂ) :=
  ((IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.conjugatePeriodKernel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))).comap
    (EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ σ).subtype).map
      (nativeEmbeddingCoordinateEquiv A ρ s hs hg hdegree σ).toLinearMap

omit [NumberField.IsCMField E] in
theorem nativeHermitianParts_isCompl :
    IsCompl (nativeHermitianPositivePart A ρ s hs hg hdegree σ)
      (nativeHermitianNegativePart A ρ s hs hg hdegree σ) := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let H := IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))
  have hact (a : E) : ComplexMultiplication.WeightOne.CM.IsHodgeMap H H (ComplexMultiplication.WeightOne.CM.scalarEndomorphism
      (U := RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))) E a) :=
    ReferenceFamily.Complex.PeriodFieldAction.IntrinsicNumberFieldAction.fieldAction_isHodgeMap A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ a
  exact (Submodule.orderIsoMapComap (nativeEmbeddingCoordinateEquiv A ρ s hs hg hdegree σ)).isCompl_iff.mp
    (EmbeddingHodgeCriterion.embeddingSpace_hodge_isCompl H hact σ)

omit [NumberField.IsCMField E] in
theorem nativeHermitianPositivePart_finrank {r : ℕ}
    (hr : LieRanks.HasLieRank A.abelian ρ (σ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) r) :
    Module.finrank ℂ (nativeHermitianPositivePart A ρ s hs hg hdegree σ) = 3 - r := by
  let S := EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ σ
  let K := (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))).ker
  have hm := (nativeEmbeddingCoordinateEquiv A ρ s hs hg hdegree σ).finrank_map_eq (K.comap S.subtype)
  have hs' := (EmbeddingHodgeCriterion.submoduleComapSwap K S).finrank_eq
  exact hm.trans (hs'.trans
    (EmbeddingHodgeRanks.IntrinsicNumberFieldAction.holomorphicEmbeddingPart_finrank A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ s hs hg hdegree σ hr))

omit [NumberField.IsCMField E] in
theorem nativeHermitianNegativePart_finrank {r : ℕ}
    (hr : LieRanks.HasLieRank A.abelian ρ (σ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) r) :
    Module.finrank ℂ (nativeHermitianNegativePart A ρ s hs hg hdegree σ) = r := by
  let S := EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ σ
  let K := IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.conjugatePeriodKernel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))
  have hm := (nativeEmbeddingCoordinateEquiv A ρ s hs hg hdegree σ).finrank_map_eq (K.comap S.subtype)
  have hs' := (EmbeddingHodgeCriterion.submoduleComapSwap K S).finrank_eq
  exact hm.trans (hs'.trans
    (EmbeddingPeriodProjection.IntrinsicNumberFieldAction.conjugateEmbeddingPart_finrank A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ σ hr))

theorem nativeHermitianPositivePart_positive (hρ : ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)
    (x : Fin 3 → ℂ) (hx : x ∈ nativeHermitianPositivePart A ρ s hs hg hdegree σ) (hne : x ≠ 0) :
    0 < (weightedEmbeddingHermitian A ρ s hs hg hdegree hρ ξ σ x x).re := by
  obtain ⟨u, hu, rfl⟩ := hx
  have hnu : u.val ≠ 0 := fun hz => hne
    ((congrArg (nativeEmbeddingCoordinateEquiv A ρ s hs hg hdegree σ) (Subtype.ext hz)).trans
      (nativeEmbeddingCoordinateEquiv A ρ s hs hg hdegree σ).map_zero)
  exact weightedEmbeddingHermitian_holomorphic_positive A ρ s hs hg hdegree hρ ξ hξ σ u.val u.property hu hnu

theorem nativeHermitianNegativePart_negative (hρ : ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)
    (x : Fin 3 → ℂ) (hx : x ∈ nativeHermitianNegativePart A ρ s hs hg hdegree σ) (hne : x ≠ 0) :
    (weightedEmbeddingHermitian A ρ s hs hg hdegree hρ ξ σ x x).re < 0 := by
  obtain ⟨u, hu, rfl⟩ := hx
  have hnu : u.val ≠ 0 := fun hz => hne
    ((congrArg (nativeEmbeddingCoordinateEquiv A ρ s hs hg hdegree σ) (Subtype.ext hz)).trans
      (nativeEmbeddingCoordinateEquiv A ρ s hs hg hdegree σ).map_zero)
  exact weightedEmbeddingHermitian_antiholomorphic_negative A ρ s hs hg hdegree hρ ξ hξ σ u.val u.property hu hnu

theorem nativeHermitianParts_orthogonal (hρ : ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)
    (x y : Fin 3 → ℂ) (hx : x ∈ nativeHermitianPositivePart A ρ s hs hg hdegree σ)
    (hy : y ∈ nativeHermitianNegativePart A ρ s hs hg hdegree σ) :
    weightedEmbeddingHermitian A ρ s hs hg hdegree hρ ξ σ x y = 0 := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  have hc := PeriodPolarization.complexChernForm_periodKernel_isotropic
    (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)) (ChernPairing.polarizationLineBundle A)
    (ChernPairing.polarizationLineBundle_ample A) u.val
    (ComplexMultiplication.WeightOne.CM.coefficientConjugation (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))) v.val) hu hv
  have he := weightedEmbeddingHermitian_Chern A ρ s hs hg hdegree hρ ξ hξ σ u.val v.val u.property
  exact he.symm.trans ((congrArg (fun z : ℂ => Complex.I * z) hc).trans (mul_zero Complex.I))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking
