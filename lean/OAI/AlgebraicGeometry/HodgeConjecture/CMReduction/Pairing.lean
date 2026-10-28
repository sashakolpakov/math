import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType
import OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Contraction

/-! # Pairing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Pairing.CM.Construction

noncomputable section

/-!
CMReduction's nonzero contraction scalar, conditional on precisely the H¹ clause
of PolarizedPairing. This concerns the constructed rational CM polarization. Identifying
the corresponding contraction with algebraic geometric operations is a
separate obligation; no such identification is assumed in this module.
-/

open scoped TensorProduct BigOperators

/-- The supplied PolarizedPairing assertion needed by the switch composition argument. -/
def PolarizedPairingInput : Prop :=
  ∀ {E U : Type}
    [Field E] [NumberField E] [Algebra ℚ E]
    [AddCommGroup U] [Module ℚ U] [Module E U]
    [IsScalarTower ℚ E U]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U)
    (P : ComplexMultiplication.CM.Polarization.WeightOnePolarization H)
    (_hCM : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H)
    (σ : E →ₐ[ℚ] ℂ)
    (u v : ComplexMultiplication.WeightOne.CM.Complexification U)
    (_hu : u ∈ ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U σ)
    (_hv : v ∈ ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ))
    (_hu0 : u ≠ 0) (_hv0 : v ≠ 0),
    P.form.baseChange ℂ u v ≠ 0

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

abbrev SignType :=
  ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)

/-- The canonical polarization value on conjugate and identity lines,
in the order encountered when composing two consecutive switches. -/
def middlePairingScalar (v : SignType E) : ℂ :=
  (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure_polarization E v).form.baseChange ℂ
    (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
      (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)))
    (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1))

theorem middlePairingScalar_ne_zero (h_PolarizedPairing : PolarizedPairingInput) (v : SignType E) :
    middlePairingScalar E v ≠ 0 := by
  let σ := ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1
  let τ := ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
    (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)
  have hconj : τ = ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ := by
    simpa only [mul_one] using ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_conjugation E 1
  have hback : ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ = σ := by
    rw [hconj, ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive]
  apply h_PolarizedPairing (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v)
    (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure_polarization E v)
    (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure_rankOneCMAction E v)
    τ (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E τ) (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E σ)
  · exact (ComplexMultiplication.EmbeddingDecomposition.CM.mem_embeddingSpace E E τ _).mpr (fun a => ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector_eigen E a τ)
  · rw [hback]
    exact (ComplexMultiplication.EmbeddingDecomposition.CM.mem_embeddingSpace E E σ _).mpr (fun a => ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector_eigen E a σ)
  · exact ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector_ne_zero E τ
  · exact ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector_ne_zero E σ

/-- All intermediate factors contribute nonzero scalars, including an
empty list, for which the product is one. -/
theorem intermediateScalar_ne_zero (h_PolarizedPairing : PolarizedPairingInput)
    (p : ℕ) (v : Fin p → SignType E) :
    (∏ i : Fin p, middlePairingScalar E (v i)) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => middlePairingScalar_ne_zero E h_PolarizedPairing (v i))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Pairing.CM.Construction
