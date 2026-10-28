import OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm
import Mathlib.Basic.Complex.BigOperators

/-! # Polarization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CM

noncomputable section

/-!
# Rational polarizations of the constructed CM Hodge structures

The trace pairing vanishes on each pure weight-one type. With the
conjugation-in-the-first-slot convention, `i · Q(u, conjugate(u))`
is real and strictly positive on every nonzero holomorphic vector.
Its positivity is an explicit sum of squared embedding coordinates with
the positive imaginary coefficients supplied by weak approximation.
Integrality on a lattice and geometric realization are separate steps.
-/

open scoped TensorProduct Classical

/-- Rational weight-one polarization data on the actual complexification.
The positivity convention is `i · Q(u, conjugate(u)) > 0` for holomorphic `u`. -/
structure Polarization.WeightOnePolarization {U : Type*} [AddCommGroup U] [Module ℚ U]
    (H : WeightOne.CM.WeightOneHodgeStructure U) where
  form : LinearMap.BilinForm ℚ U
  alternating : form.IsAlt
  nondegenerate : form.Nondegenerate
  holomorphic_isotropic : ∀ u ∈ H.holomorphic, ∀ v ∈ H.holomorphic, form.baseChange ℂ u v = 0
  hodge_self_real : ∀ u, (Complex.I * form.baseChange ℂ u (WeightOne.CM.coefficientConjugation U u)).im = 0
  hodge_positive : ∀ u ∈ H.holomorphic, u ≠ 0 →
    0 < (Complex.I * form.baseChange ℂ u (WeightOne.CM.coefficientConjugation U u)).re

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

/-- Reindexing the trace formula by conjugate embeddings gives its sesquilinear expression. -/
theorem Polarization.cmTracePairing_conjugate (ξ : E) (u v : WeightOne.CM.Complexification E) :
    (TraceForm.cmTracePairing E ξ).baseChange ℂ u (WeightOne.CM.coefficientConjugation E v) =
      ∑ σ : E →ₐ[ℚ] ℂ, star (σ ξ) * EmbeddingDecomposition.CM.fieldComplexificationEquiv E u σ *
        star (EmbeddingDecomposition.CM.fieldComplexificationEquiv E v σ) := by
  rw [TraceForm.cmTracePairing_complex]
  simp only [TypeHodgeStructure.fieldComplexificationEquiv_conjugation]
  let e : Equiv.Perm (E →ₐ[ℚ] ℂ) :=
    ⟨EmbeddingHodgeType.CM.conjugateEmbedding, EmbeddingHodgeType.CM.conjugateEmbedding, EmbeddingHodgeType.CM.conjugateEmbedding_involutive, EmbeddingHodgeType.CM.conjugateEmbedding_involutive⟩
  let f (σ : E →ₐ[ℚ] ℂ) := σ ξ * EmbeddingDecomposition.CM.fieldComplexificationEquiv E u (EmbeddingHodgeType.CM.conjugateEmbedding σ) *
    star (EmbeddingDecomposition.CM.fieldComplexificationEquiv E v (EmbeddingHodgeType.CM.conjugateEmbedding σ))
  change (∑ σ, f σ) = _
  rw [← Equiv.sum_comp e f]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [f, e, Equiv.coe_fn_mk, EmbeddingHodgeType.CM.conjugateEmbedding_involutive, EmbeddingHodgeType.CM.conjugateEmbedding_apply]

/-- The imaginary coefficient is the weight of the squared coordinate in the Hodge metric. -/
theorem Polarization.complex_trace_positive_weight (z a : ℂ) :
    (Complex.I * (star z * a * star a)).re = z.im * Complex.normSq a := by
  change (Complex.I * ((starRingEnd ℂ) z * a * (starRingEnd ℂ) a)).re = _
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, Complex.normSq_apply]
  ring

theorem Polarization.complex_trace_real_weight (z a : ℂ) :
    (star z * a * star a).re = z.re * Complex.normSq a := by
  change ((starRingEnd ℂ) z * a * (starRingEnd ℂ) a).re = _
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

/-- The Hodge metric is the weighted sum of squared embedding coordinates. -/
theorem Polarization.cmTracePairing_hodge_norm (ξ : E) (u : WeightOne.CM.Complexification E) :
    (Complex.I * (TraceForm.cmTracePairing E ξ).baseChange ℂ u (WeightOne.CM.coefficientConjugation E u)).re =
      ∑ σ : E →ₐ[ℚ] ℂ, (σ ξ).im * Complex.normSq (EmbeddingDecomposition.CM.fieldComplexificationEquiv E u σ) := by
  rw [Polarization.cmTracePairing_conjugate, Finset.mul_sum, Complex.re_sum]
  exact Finset.sum_congr rfl (fun σ _ => Polarization.complex_trace_positive_weight _ _)

variable {E} (ε : TypeHodgeStructure.CMEmbeddingType E)

/-- The trace pairing vanishes on pairs of vectors of the same pure Hodge type. -/
theorem TypeHodgeStructure.CMEmbeddingType.tracePairing_type_isotropic (b : Bool) (u v : WeightOne.CM.Complexification E)
    (hu : u ∈ ε.subspace b) (hv : v ∈ ε.subspace b) :
    ε.tracePairing.baseChange ℂ u v = 0 := by
  rw [TypeHodgeStructure.CMEmbeddingType.tracePairing, TraceForm.cmTracePairing_complex]
  apply Finset.sum_eq_zero
  intro σ _
  by_cases hz : EmbeddingDecomposition.CM.fieldComplexificationEquiv E u (EmbeddingHodgeType.CM.conjugateEmbedding σ) = 0
  · simp only [hz, mul_zero, zero_mul]
  · have hs := (ε.mem_subspace_iff b u).mp hu (EmbeddingHodgeType.CM.conjugateEmbedding σ) hz
    have ht : EmbeddingDecomposition.CM.fieldComplexificationEquiv E v σ = 0 := by
      by_contra hn
      have he := (ε.mem_subspace_iff b v).mp hv σ hn
      rw [ε.property, he] at hs
      cases b <;> simp at hs
    simp only [ht, mul_zero]

/-- Alternation of the rational trace form gives a real self-pairing after multiplication by `i`. -/
theorem TypeHodgeStructure.CMEmbeddingType.tracePairing_hodge_self_real (u : WeightOne.CM.Complexification E) :
    (Complex.I * ε.tracePairing.baseChange ℂ u (WeightOne.CM.coefficientConjugation E u)).im = 0 := by
  rw [TypeHodgeStructure.CMEmbeddingType.tracePairing, Polarization.cmTracePairing_conjugate]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
    Complex.re_sum]
  apply Finset.sum_eq_zero
  intro σ _
  rw [Polarization.complex_trace_real_weight, ε.imaginaryElement_re, zero_mul]

/-- The constructed trace form satisfies strict Hodge positivity. -/
theorem TypeHodgeStructure.CMEmbeddingType.tracePairing_hodge_positive (u : WeightOne.CM.Complexification E) (hu : u ∈ ε.hodgeStructure.holomorphic)
    (hne : u ≠ 0) :
    0 < (Complex.I * ε.tracePairing.baseChange ℂ u (WeightOne.CM.coefficientConjugation E u)).re := by
  rw [TypeHodgeStructure.CMEmbeddingType.tracePairing, Polarization.cmTracePairing_hodge_norm]
  have hsign : ∀ σ, EmbeddingDecomposition.CM.fieldComplexificationEquiv E u σ ≠ 0 → ε.val σ = true :=
    (ε.mem_subspace_iff true u).mp hu
  have hpos (σ : E →ₐ[ℚ] ℂ) (hσ : EmbeddingDecomposition.CM.fieldComplexificationEquiv E u σ ≠ 0) :
      0 < (σ ε.imaginaryElement).im * Complex.normSq (EmbeddingDecomposition.CM.fieldComplexificationEquiv E u σ) :=
    mul_pos (ε.imaginaryElement_positive σ (hsign σ hσ)) (Complex.normSq_pos.mpr hσ)
  have hn : ∀ σ ∈ (Finset.univ : Finset (E →ₐ[ℚ] ℂ)),
      0 ≤ (σ ε.imaginaryElement).im * Complex.normSq (EmbeddingDecomposition.CM.fieldComplexificationEquiv E u σ) := by
    intro σ _
    by_cases hσ : EmbeddingDecomposition.CM.fieldComplexificationEquiv E u σ = 0
    · simp [hσ]
    · exact (hpos σ hσ).le
  apply (Finset.sum_pos_iff_of_nonneg hn).mpr
  have hex : ∃ σ : E →ₐ[ℚ] ℂ, EmbeddingDecomposition.CM.fieldComplexificationEquiv E u σ ≠ 0 := by
    by_contra! hz
    apply hne
    apply (EmbeddingDecomposition.CM.fieldComplexificationEquiv E).injective
    apply funext
    intro σ
    simpa only [map_zero, Pi.zero_apply] using hz σ
  obtain ⟨σ, hσ⟩ := hex
  exact ⟨σ, Finset.mem_univ σ, hpos σ hσ⟩

/-- Every constructed rank-one CM Hodge structure is rationally polarizable. -/
def TypeHodgeStructure.CMEmbeddingType.polarization : Polarization.WeightOnePolarization ε.hodgeStructure where
  form := ε.tracePairing
  alternating := ε.tracePairing_isAlt
  nondegenerate := ε.tracePairing_nondegenerate
  holomorphic_isotropic u hu v hv := ε.tracePairing_type_isotropic true u v hu hv
  hodge_self_real := ε.tracePairing_hodge_self_real
  hodge_positive := ε.tracePairing_hodge_positive

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CM
