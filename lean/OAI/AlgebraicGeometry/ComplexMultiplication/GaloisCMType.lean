import OAI.AlgebraicGeometry.ComplexMultiplication.CM.Polarization
import OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorSignReduction

/-! # Galois CM Type -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField

noncomputable section

/-!
# Realizing odd Galois sign functions as rank-one CM Hodge structures

Normality identifies the actual complex embeddings of the common field
with its Galois group, respecting CM conjugation. Every odd function
appearing in a switch chain therefore determines a weight-one Hodge
structure on the rational vector space of the common field, with the
prescribed type on each embedding line. These are linear Hodge structures;
their geometric realization is not asserted here.
-/

open scoped Classical

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsGalois ℚ K]
  [NumberField.IsCMField K]

/-- Actual complex embeddings of a normal coefficient field are its Galois automorphisms. -/
def galoisEmbeddingEquiv : Gal(K/ℚ) ≃ (K →ₐ[ℚ] ℂ) :=
  (Normal.algHomEquivAut ℚ ℂ K).symm

omit [NumberField K] [NumberField.IsCMField K] in
@[simp]
theorem galoisEmbeddingEquiv_apply (g : Gal(K/ℚ)) (x : K) :
    galoisEmbeddingEquiv K g x = (g x : ℂ) := rfl

/-- The embedding identification respects the conjugation pairing used in switches. -/
theorem galoisEmbeddingEquiv_conjugation (g : Gal(K/ℚ)) :
    galoisEmbeddingEquiv K (GaloisSigns.CM.CMCoefficientField.conjugation K * g) =
      EmbeddingHodgeType.CM.conjugateEmbedding (galoisEmbeddingEquiv K g) := by
  ext x
  exact GaloisSigns.CM.CMCoefficientField.conjugation_coe K (g x)

/-- Regard an odd Galois sign function as an odd type on complex embeddings. -/
def embeddingType (v : OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => GaloisSigns.CM.CMCoefficientField.conjugation K * g)) :
    CM.TypeHodgeStructure.CMEmbeddingType K := by
  refine ⟨fun σ => v.val ((galoisEmbeddingEquiv K).symm σ), ?_⟩
  intro σ
  have he : (galoisEmbeddingEquiv K).symm (EmbeddingHodgeType.CM.conjugateEmbedding σ) =
      GaloisSigns.CM.CMCoefficientField.conjugation K * (galoisEmbeddingEquiv K).symm σ := by
    apply (galoisEmbeddingEquiv K).injective
    rw [Equiv.apply_symm_apply, galoisEmbeddingEquiv_conjugation, Equiv.apply_symm_apply]
  exact (congrArg v.val he).trans (v.property _)

@[simp]
theorem embeddingType_apply (v : OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (g : Gal(K/ℚ)) : (embeddingType K v).val (galoisEmbeddingEquiv K g) = v.val g := by
  exact congrArg v.val ((galoisEmbeddingEquiv K).symm_apply_apply g)

/-- Construct the weight-one rational Hodge structure for any intermediate switch type. -/
def hodgeStructure (v : OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => GaloisSigns.CM.CMCoefficientField.conjugation K * g)) :
    WeightOne.CM.WeightOneHodgeStructure K := (embeddingType K v).hodgeStructure

/-- The common field acts with rank one and preserves the constructed Hodge structure. -/
theorem hodgeStructure_rankOneCMAction
    (v : OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => GaloisSigns.CM.CMCoefficientField.conjugation K * g)) :
    WeightOne.CM.RankOneCMAction K (CMCoefficientField.hodgeStructure K v) := (embeddingType K v).rankOneCMAction

/-- The holomorphic embedding lines have exactly the specified Galois signs. -/
theorem hodgeStructure_holomorphic
    (v : OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => GaloisSigns.CM.CMCoefficientField.conjugation K * g)) (g : Gal(K/ℚ)) :
    EmbeddingDecomposition.CM.embeddingVector K (galoisEmbeddingEquiv K g) ∈ (CMCoefficientField.hodgeStructure K v).holomorphic ↔
      v.val g = true := by
  change EmbeddingDecomposition.CM.embeddingVector K (galoisEmbeddingEquiv K g) ∈
    (embeddingType K v).subspace true ↔ _
  rw [CM.TypeHodgeStructure.CMEmbeddingType.embeddingVector_mem_subspace, embeddingType_apply]

/-- The antiholomorphic embedding lines have exactly the opposite signs. -/
theorem hodgeStructure_antiholomorphic
    (v : OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => GaloisSigns.CM.CMCoefficientField.conjugation K * g)) (g : Gal(K/ℚ)) :
    EmbeddingDecomposition.CM.embeddingVector K (galoisEmbeddingEquiv K g) ∈ (CMCoefficientField.hodgeStructure K v).antiholomorphic ↔
      v.val g = false := by
  change EmbeddingDecomposition.CM.embeddingVector K (galoisEmbeddingEquiv K g) ∈
    (embeddingType K v).subspace false ↔ _
  rw [CM.TypeHodgeStructure.CMEmbeddingType.embeddingVector_mem_subspace, embeddingType_apply]

/-- Computing the embedding signs of the constructed CM action recovers the
original odd Galois function exactly. -/
theorem hodgeStructure_embeddingSign
    (v : OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => GaloisSigns.CM.CMCoefficientField.conjugation K * g)) (g : Gal(K/ℚ)) :
    (hodgeStructure_rankOneCMAction K v).embeddingSign (galoisEmbeddingEquiv K g) =
      v.val g :=
  ((embeddingType K v).embeddingSign_eq (galoisEmbeddingEquiv K g)).trans
    (embeddingType_apply K v g)

/-- Every intermediate odd Galois type carries the constructed rational trace polarization. -/
def hodgeStructure_polarization
    (v : OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => GaloisSigns.CM.CMCoefficientField.conjugation K * g)) :
    CM.Polarization.WeightOnePolarization (CMCoefficientField.hodgeStructure K v) := (embeddingType K v).polarization

end

end OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField
