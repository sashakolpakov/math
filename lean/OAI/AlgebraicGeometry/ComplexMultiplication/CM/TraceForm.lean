import OAI.AlgebraicGeometry.ComplexMultiplication.CM.ImaginaryElement
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.RingTheory.Trace.Basic

/-! # Trace Form -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CM

noncomputable section

/-!
# The rational trace pairing for a CM type

For a totally imaginary element `ξ`, the pairing is
`(x,y) ↦ Tr(ξ · c(x) · y)`. It is alternating, and is nondegenerate
whenever `ξ` is nonzero. The scalar extension is computed in the actual
embedding coordinates, preparing its Hodge positivity calculation.
-/

open scoped TensorProduct Classical

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

/-- Intrinsic CM conjugation as a rational algebra automorphism. -/
def TraceForm.cmFieldConjugation : E ≃ₐ[ℚ] E :=
  (NumberField.IsCMField.complexConj E).restrictScalars ℚ

@[simp]
theorem TraceForm.cmFieldConjugation_involutive (x : E) : TraceForm.cmFieldConjugation E (TraceForm.cmFieldConjugation E x) = x :=
  NumberField.IsCMField.complexConj_apply_apply E x

theorem TraceForm.cmFieldConjugation_embedding (σ : E →ₐ[ℚ] ℂ) (x : E) :
    σ (TraceForm.cmFieldConjugation E x) = star (σ x) :=
  NumberField.IsCMField.complexEmbedding_complexConj E σ.toRingHom x

/-- The rational trace pairing, with conjugation in its first slot. -/
def TraceForm.cmTracePairing (ξ : E) : LinearMap.BilinForm ℚ E :=
  (Algebra.traceForm ℚ E).compl₁₂ (ξ • (TraceForm.cmFieldConjugation E).toLinearMap) LinearMap.id

@[simp]
theorem TraceForm.cmTracePairing_apply (ξ x y : E) :
    TraceForm.cmTracePairing E ξ x y = Algebra.trace ℚ E (ξ * TraceForm.cmFieldConjugation E x * y) := rfl

/-- A totally imaginary coefficient makes the trace pairing skew-symmetric. -/
theorem TraceForm.cmTracePairing_skew (ξ : E) (hξ : TraceForm.cmFieldConjugation E ξ = -ξ) (x y : E) :
    TraceForm.cmTracePairing E ξ x y = -TraceForm.cmTracePairing E ξ y x := by
  calc
    TraceForm.cmTracePairing E ξ x y =
        Algebra.trace ℚ E (TraceForm.cmFieldConjugation E (ξ * TraceForm.cmFieldConjugation E x * y)) :=
      (Algebra.trace_eq_of_algEquiv (TraceForm.cmFieldConjugation E) _).symm
    _ = Algebra.trace ℚ E (-(ξ * TraceForm.cmFieldConjugation E y * x)) := by
      congr 1
      rw [map_mul, map_mul, hξ, TraceForm.cmFieldConjugation_involutive]
      ring
    _ = -TraceForm.cmTracePairing E ξ y x := map_neg _ _

theorem TraceForm.cmTracePairing_isAlt (ξ : E) (hξ : TraceForm.cmFieldConjugation E ξ = -ξ) :
    (TraceForm.cmTracePairing E ξ).IsAlt := by
  intro x
  have hs := TraceForm.cmTracePairing_skew E ξ hξ x x
  linarith

/-- Nondegeneracy follows from the separable field trace and the invertibility of `ξ`. -/
theorem TraceForm.cmTracePairing_nondegenerate (ξ : E) (hξ : ξ ≠ 0) :
    (TraceForm.cmTracePairing E ξ).Nondegenerate := by
  constructor
  · intro x hx
    have hz : ξ * TraceForm.cmFieldConjugation E x = 0 :=
      (traceForm_nondegenerate ℚ E).1 _ hx
    have hc := (mul_eq_zero.mp hz).resolve_left hξ
    apply (TraceForm.cmFieldConjugation E).injective
    simpa only [map_zero] using hc
  · intro y hy
    apply (traceForm_nondegenerate ℚ E).2 y
    intro z
    change Algebra.trace ℚ E (z * y) = 0
    have hz := hy (TraceForm.cmFieldConjugation E (ξ⁻¹ * z))
    simpa only [TraceForm.cmTracePairing_apply, TraceForm.cmFieldConjugation_involutive, ← mul_assoc,
      mul_inv_cancel₀ hξ, one_mul] using hz

/-- The actual complex base change of the rational pairing, expressed in embedding coordinates. -/
theorem TraceForm.cmTracePairing_complex (ξ : E) (u v : WeightOne.CM.Complexification E) :
    (TraceForm.cmTracePairing E ξ).baseChange ℂ u v =
      ∑ σ : E →ₐ[ℚ] ℂ, σ ξ * EmbeddingDecomposition.CM.fieldComplexificationEquiv E u (EmbeddingHodgeType.CM.conjugateEmbedding σ) *
        EmbeddingDecomposition.CM.fieldComplexificationEquiv E v σ := by
  induction u using TensorProduct.inductionOn with
  | add u w hu hw =>
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, hu, hw, mul_add, add_mul,
      Finset.sum_add_distrib]
  | tmul a x =>
    induction v using TensorProduct.inductionOn with
    | add v w hv hw =>
      simp only [map_add, Pi.add_apply, hv, hw, mul_add, Finset.sum_add_distrib]
    | tmul b y =>
      rw [LinearMap.BilinForm.baseChange_tmul, TraceForm.cmTracePairing_apply]
      change algebraMap ℚ ℂ (Algebra.trace ℚ E (ξ * TraceForm.cmFieldConjugation E x * y)) * (a * b) = _
      rw [trace_eq_sum_embeddings ℂ]
      simp only [map_mul, TraceForm.cmFieldConjugation_embedding, EmbeddingDecomposition.CM.fieldComplexificationEquiv_tmul,
        EmbeddingHodgeType.CM.conjugateEmbedding_apply]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      ring

variable {E} (ε : TypeHodgeStructure.CMEmbeddingType E)

/-- The rational pairing associated to the imaginary element constructed by weak approximation. -/
def TypeHodgeStructure.CMEmbeddingType.tracePairing : LinearMap.BilinForm ℚ E := TraceForm.cmTracePairing E ε.imaginaryElement

theorem TypeHodgeStructure.CMEmbeddingType.tracePairing_isAlt : ε.tracePairing.IsAlt :=
  TraceForm.cmTracePairing_isAlt E ε.imaginaryElement ε.imaginaryElement_conjugate

theorem TypeHodgeStructure.CMEmbeddingType.tracePairing_nondegenerate : ε.tracePairing.Nondegenerate :=
  TraceForm.cmTracePairing_nondegenerate E ε.imaginaryElement ε.imaginaryElement_ne_zero

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CM
