import OAI.AlgebraicGeometry.ComplexMultiplication.CM.LineTransfer
import Mathlib.LinearAlgebra.BilinearMap

/-! # Coefficient Vectors -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CoefficientVectors.CM.Construction

noncomputable section

/-! Canonical embedding vectors over the finite coefficient field and
their actual scalar Galois action. These support the unchanged-slot tensors
without assuming that arbitrary complex Hodge vectors descend to ℚ. -/

open scoped TensorProduct Classical

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]

def coefficientVector (g : Gal(E/ℚ)) : E ⊗[ℚ] E :=
  (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E)).symm
    (Pi.single (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E g) 1)

theorem coefficientVector_coordinates (g : Gal(E/ℚ)) :
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E)
      (coefficientVector E g) = Pi.single (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E g) 1 :=
  LinearEquiv.apply_symm_apply _ _

omit [NumberField E] in
theorem self_coefficientEmbedding (g : Gal(E/ℚ)) (x : E) :
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientEmbedding E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E)
      (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E g) x = g x := by
  apply Subtype.ext
  rfl

theorem coefficientCoordinates_conjugate (g τ : Gal(E/ℚ)) (x : E ⊗[ℚ] E) :
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E)
      (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E E g x) (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (g * τ)) =
    g (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E)
      x (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul a b =>
      simp only [ComplexMultiplication.ScalarDescent.CM.scalarConjugate_tmul, ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv_tmul,
        self_coefficientEmbedding, map_mul]
      rfl

theorem coefficientVector_conjugate (g τ : Gal(E/ℚ)) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E E g (coefficientVector E τ) = coefficientVector E (g * τ) := by
  apply (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E)).injective
  funext σ
  obtain ⟨κ, rfl⟩ := (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).surjective σ
  obtain ⟨κ, rfl⟩ := (Equiv.mulLeft g).surjective κ
  change ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E)
      (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E E g (coefficientVector E τ))
      (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (g * κ)) =
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E)
      (coefficientVector E (g * τ)) (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (g * κ))
  rw [coefficientCoordinates_conjugate, coefficientVector_coordinates,
    coefficientVector_coordinates]
  by_cases h : τ = κ
  · subst κ
    simp
  · have h₁ : ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ ≠
        ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E κ :=
      (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).injective.ne h
    have h₂ : ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (g * τ) ≠
        ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (g * κ) :=
      (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).injective.ne
        (fun he => h (mul_left_cancel he))
    simp [h₁, h₂]

theorem coefficientCoordinates_inclusion (x : E ⊗[ℚ] E) (σ : E →ₐ[ℚ] ℂ) :
    ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion E E x) σ =
      (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E) x σ : ℂ) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, IntermediateField.coe_add]
  | tmul a b =>
      simp only [ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion_tmul, ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv_tmul,
        ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientFieldEquiv_tmul, IntermediateField.coe_mul, ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientEmbedding_coe]

theorem coefficientVector_inclusion (g : Gal(E/ℚ)) :
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion E E (coefficientVector E g) =
      ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E g) := by
  apply (ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E).injective
  funext σ
  rw [coefficientCoordinates_inclusion, coefficientVector_coordinates,
    ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv_embeddingVector]
  by_cases h : ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E g = σ <;>
    simp [h]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CoefficientVectors.CM.Construction
