import OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.LineMap
import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType

/-! # Line Transfer -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

/-!
# Transferring a common-field CM line into the original Hodge structure

For each embedding line in an actual CM decomposition, use its odd Galois
sign function to construct a rank-one Hodge structure on the common field.
The map from its identity embedding line to the original line, zero on all
other source lines, is a complex linear combination of rational Hodge maps.
This proves the linear transfer step of the manuscript. Turning these
Hodge maps into algebraic homomorphisms remains a geometric step.
-/

open scoped TensorProduct Classical

namespace CM.LineTransfer.CMCoefficientField

variable (K : IntermediateField ℚ ℂ) [IsGalois ℚ K]

/-- Every complex embedding of a normal coefficient field has values in that field. -/
theorem embedding_fieldRange_le (σ : K →ₐ[ℚ] ℂ) : σ.fieldRange ≤ K := by
  obtain ⟨g, rfl⟩ := (GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K).surjective σ
  rintro z ⟨x, rfl⟩
  exact (g x).property

/-- Applying scalar conjugation to the identity embedding gives the corresponding Galois label. -/
theorem galoisCoefficientEmbedding_identity (g : Gal(K/ℚ)) :
    EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K K (embedding_fieldRange_le K) g (GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K 1) =
      GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K g := by
  ext x
  have hx : EmbeddingCoefficientField.CM.coefficientEmbedding K K (embedding_fieldRange_le K) (GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K 1) x = x := by
    apply Subtype.ext
    rfl
  exact congrArg (fun z : K => (g z : ℂ)) hx

end CM.LineTransfer.CMCoefficientField

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
variable {H : WeightOne.CM.WeightOneHodgeStructure U} (D : Decomposition.CM.CMDecomposition H)

/-- The common-field Hodge structure whose Galois signs match the chosen original line. -/
def Decomposition.CM.CMDecomposition.embeddingLineSource (j : D.EmbeddingIndex) : WeightOne.CM.WeightOneHodgeStructure D.commonCoefficientField :=
  GaloisCMType.CM.CMCoefficientField.hodgeStructure D.commonCoefficientField (D.galoisOddSign j)

theorem Decomposition.CM.CMDecomposition.embeddingLineSource_cm (j : D.EmbeddingIndex) :
    WeightOne.CM.RankOneCMAction D.commonCoefficientField (D.embeddingLineSource j) :=
  GaloisCMType.CM.CMCoefficientField.hodgeStructure_rankOneCMAction D.commonCoefficientField (D.galoisOddSign j)

/-- The selected identity line maps to the original embedding line and all other lines map to zero. -/
def Decomposition.CM.CMDecomposition.embeddingLineTransfer (j : D.EmbeddingIndex) :
    WeightOne.CM.Complexification D.commonCoefficientField →ₗ[ℂ] WeightOne.CM.Complexification U :=
  Coefficient.LineMap.CM.basisLineMap (D.embeddingLineSource_cm j).embeddingBasis D.embeddingBasis
    (GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv D.commonCoefficientField 1) j

theorem Decomposition.CM.CMDecomposition.embeddingLineTransfer_basis (j : D.EmbeddingIndex)
    (σ : D.commonCoefficientField →ₐ[ℚ] ℂ) :
    D.embeddingLineTransfer j ((D.embeddingLineSource_cm j).embeddingBasis σ) =
      if σ = GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv D.commonCoefficientField 1
      then D.embeddingBasis j else 0 := Coefficient.LineMap.CM.basisLineMap_basis _ _ _ _ _

theorem Decomposition.CM.CMDecomposition.embeddingLineTransfer_ne_zero (j : D.EmbeddingIndex) : D.embeddingLineTransfer j ≠ 0 :=
  Coefficient.LineMap.CM.basisLineMap_ne_zero _ _ _ _

/-- The line transfer used in the CM reduction is a scalar combination of rational Hodge maps. -/
theorem Decomposition.CM.CMDecomposition.embeddingLineTransfer_mem_rationalHodgeMapSpan (j : D.EmbeddingIndex) :
    D.embeddingLineTransfer j ∈ Hodge.MapDescent.CM.rationalHodgeMapSpan (D.embeddingLineSource j) H := by
  let h := D.embeddingLineSource_cm j
  let hK := CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le D.commonCoefficientField
  refine Coefficient.LineMap.CM.basisLineMap_mem_rationalHodgeMapSpan (U := D.commonCoefficientField) (V := U)
    (ι := D.commonCoefficientField →ₐ[ℚ] ℂ) (κ := D.EmbeddingIndex)
    D.commonCoefficientField (D.embeddingLineSource j) H
    (h.coefficientEmbeddingBasis D.commonCoefficientField hK) D.coefficientEmbeddingBasis
    h.embeddingBasis D.embeddingBasis
    (h.coefficientInclusion_embeddingBasis D.commonCoefficientField hK) ?_
    (EmbeddingCoefficientField.CM.galoisCoefficientEmbeddingEquiv D.commonCoefficientField D.commonCoefficientField hK)
    D.galoisIndexEquiv
    (h.scalarConjugate_coefficientEmbeddingBasis D.commonCoefficientField hK) ?_
    h.embeddingSign D.embeddingSign ?_ ?_
    (GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv D.commonCoefficientField 1) j ?_
  · intro k
    change EmbeddingCoefficientField.CM.coefficientInclusion D.commonCoefficientField U (D.coefficientEmbeddingBasis k) =
      D.embeddingBasis k
    exact Decomposition.CM.CMDecomposition.coefficientInclusion_embeddingBasis D k
  · intro g k
    change ScalarDescent.CM.scalarConjugate ℚ D.commonCoefficientField U g (D.coefficientEmbeddingBasis k) =
      D.coefficientEmbeddingBasis (D.galoisIndex g k)
    exact Decomposition.CM.CMDecomposition.scalarConjugate_coefficientEmbeddingBasis D g k
  · intro e
    cases e
    · exact h.antiholomorphic_eq_span_embeddingBasis
    · exact h.holomorphic_eq_span_embeddingBasis
  · intro k
    exact D.embeddingBasis_mem_signSubspace k
  · intro g
    change h.embeddingSign
      (EmbeddingCoefficientField.CM.galoisCoefficientEmbedding D.commonCoefficientField D.commonCoefficientField hK g
        (GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv D.commonCoefficientField 1)) =
        D.embeddingSign (D.galoisIndex g j)
    rw [CM.LineTransfer.CMCoefficientField.galoisCoefficientEmbedding_identity]
    exact GaloisCMType.CM.CMCoefficientField.hodgeStructure_embeddingSign D.commonCoefficientField (D.galoisOddSign j) g

end

end OAI.AlgebraicGeometry.ComplexMultiplication
