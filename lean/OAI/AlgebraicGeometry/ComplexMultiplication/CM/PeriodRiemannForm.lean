import OAI.AlgebraicGeometry.ComplexMultiplication.CM.IntegralPolarization
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace

/-! # Period Riemann Form -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CM

noncomputable section

/-!
# An integral positive Riemann form on the CM period lattice

The weighted sum of the usual oriented area forms on the selected complex
coordinates is real bilinear, alternating, invariant under the complex
structure, and positive on `(z, i z)`. With the weights coming from the
integral imaginary element, it agrees with the negative field-trace pairing
on the embedded field. In particular it is integer-valued on the actual
period lattice. No projectivity criterion is assumed or proved here.
-/

open scoped Classical _root_.NumberField

open _root_.NumberField

variable (E : Type*) [Field E] [NumberField E]

/-- Weighted oriented area on the complex coordinates of the period space. -/
def PeriodRiemannForm.cmPeriodForm (w : InfinitePlace E → ℝ) : LinearMap.BilinForm ℝ (PeriodSpace.CMPeriodSpace E) :=
  ∑ v, w v • ((Complex.reLm.smulRight Complex.imLm - Complex.imLm.smulRight Complex.reLm).compl₁₂
    (LinearMap.proj v) (LinearMap.proj v))

theorem PeriodRiemannForm.cmPeriodForm_apply (w : InfinitePlace E → ℝ) (x y : PeriodSpace.CMPeriodSpace E) :
    PeriodRiemannForm.cmPeriodForm E w x y = ∑ v, w v * ((x v).re * (y v).im - (x v).im * (y v).re) := by
  simp [PeriodRiemannForm.cmPeriodForm, LinearMap.smulRight_apply]

theorem PeriodRiemannForm.cmPeriodForm_isAlt (w : InfinitePlace E → ℝ) : (PeriodRiemannForm.cmPeriodForm E w).IsAlt := by
  intro x
  simp [PeriodRiemannForm.cmPeriodForm_apply, mul_comm]

theorem PeriodRiemannForm.cmPeriodForm_complex_invariant (w : InfinitePlace E → ℝ) (x y : PeriodSpace.CMPeriodSpace E) :
    PeriodRiemannForm.cmPeriodForm E w (Complex.I • x) (Complex.I • y) = PeriodRiemannForm.cmPeriodForm E w x y := by
  rw [PeriodRiemannForm.cmPeriodForm_apply, PeriodRiemannForm.cmPeriodForm_apply]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  ring

theorem PeriodRiemannForm.cmPeriodForm_complex_self (w : InfinitePlace E → ℝ) (x : PeriodSpace.CMPeriodSpace E) :
    PeriodRiemannForm.cmPeriodForm E w x (Complex.I • x) = ∑ v, w v * Complex.normSq (x v) := by
  rw [PeriodRiemannForm.cmPeriodForm_apply]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.normSq_apply]
  ring

theorem PeriodRiemannForm.cmPeriodForm_positive (w : InfinitePlace E → ℝ) (hw : ∀ v, 0 < w v)
    (x : PeriodSpace.CMPeriodSpace E) (hx : x ≠ 0) : 0 < PeriodRiemannForm.cmPeriodForm E w x (Complex.I • x) := by
  rw [PeriodRiemannForm.cmPeriodForm_complex_self]
  have hn : ∀ v ∈ (Finset.univ : Finset (InfinitePlace E)),
      0 ≤ w v * Complex.normSq (x v) :=
    fun v _ => mul_nonneg (hw v).le (Complex.normSq_nonneg _)
  apply (Finset.sum_pos_iff_of_nonneg hn).mpr
  have he : ∃ v, x v ≠ 0 := by
    by_contra! he
    exact hx (funext he)
  obtain ⟨v, hv⟩ := he
  exact ⟨v, Finset.mem_univ v, mul_pos (hw v) (Complex.normSq_pos.mpr hv)⟩

variable [Algebra ℚ E] [IsCMField E]

variable {E} (ε : TypeHodgeStructure.CMEmbeddingType E)

/-- Pairing conjugate embeddings identifies the area form with the negative field trace. -/
theorem TypeHodgeStructure.CMEmbeddingType.cmPeriodForm_trace (ξ : E) (hξ : ∀ σ : E →ₐ[ℚ] ℂ, (σ ξ).re = 0) (x y : E) :
    PeriodRiemannForm.cmPeriodForm E (fun v => 2 * (ε.placeEmbedding v ξ).im)
      (ε.periodEmbedding x) (ε.periodEmbedding y) = -(TraceForm.cmTracePairing E ξ x y : ℝ) := by
  have ht := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E)
    (x := ξ * TraceForm.cmFieldConjugation E x * y)
  rw [ε.sum_embeddings_eq_sum_places] at ht
  have hr := congrArg Complex.re ht
  simp only [Complex.re_sum, Complex.add_re, EmbeddingHodgeType.CM.conjugateEmbedding_apply] at hr
  change (TraceForm.cmTracePairing E ξ x y : ℝ) = _ at hr
  rw [PeriodRiemannForm.cmPeriodForm_apply, hr, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro v _
  simp only [TypeHodgeStructure.CMEmbeddingType.periodEmbedding_apply, map_mul, TraceForm.cmFieldConjugation_embedding]
  change 2 * (ε.placeEmbedding v ξ).im *
      ((ε.placeEmbedding v x).re * (ε.placeEmbedding v y).im -
        (ε.placeEmbedding v x).im * (ε.placeEmbedding v y).re) =
    -((ε.placeEmbedding v ξ * (starRingEnd ℂ) (ε.placeEmbedding v x) * ε.placeEmbedding v y).re +
      ((starRingEnd ℂ)
        (ε.placeEmbedding v ξ * (starRingEnd ℂ) (ε.placeEmbedding v x) * ε.placeEmbedding v y)).re)
  simp only [Complex.conj_re, Complex.mul_re, Complex.mul_im, Complex.conj_im, hξ]
  ring

/-- The area form with integral imaginary coefficients supplied by weak approximation. -/
def TypeHodgeStructure.CMEmbeddingType.periodRiemannForm : LinearMap.BilinForm ℝ (PeriodSpace.CMPeriodSpace E) :=
  PeriodRiemannForm.cmPeriodForm E (fun v =>
    2 * (ε.placeEmbedding v (ε.polarizationMultiplier • ε.imaginaryElement)).im)

theorem TypeHodgeStructure.CMEmbeddingType.periodRiemannForm_isAlt : ε.periodRiemannForm.IsAlt := PeriodRiemannForm.cmPeriodForm_isAlt E _

theorem TypeHodgeStructure.CMEmbeddingType.periodRiemannForm_complex_invariant (x y : PeriodSpace.CMPeriodSpace E) :
    ε.periodRiemannForm (Complex.I • x) (Complex.I • y) = ε.periodRiemannForm x y :=
  PeriodRiemannForm.cmPeriodForm_complex_invariant E _ x y

theorem TypeHodgeStructure.CMEmbeddingType.periodRiemannForm_positive (x : PeriodSpace.CMPeriodSpace E) (hx : x ≠ 0) :
    0 < ε.periodRiemannForm x (Complex.I • x) := by
  apply PeriodRiemannForm.cmPeriodForm_positive E _ _ x hx
  intro v
  apply mul_pos (by norm_num : (0 : ℝ) < 2)
  rw [map_nsmul, Complex.im_nsmul, nsmul_eq_mul]
  exact mul_pos (by exact_mod_cast ε.polarizationMultiplier_pos)
    (ε.imaginaryElement_positive _ (ε.placeEmbedding_positive v))

/-- Positivity forces the alternating form to have zero left and right kernels. -/
theorem TypeHodgeStructure.CMEmbeddingType.periodRiemannForm_nondegenerate : ε.periodRiemannForm.Nondegenerate := by
  constructor
  · intro x hx
    by_contra hne
    exact (ε.periodRiemannForm_positive x hne).ne' (hx (Complex.I • x))
  · intro y hy
    by_contra hne
    have hz : ε.periodRiemannForm y (Complex.I • y) = 0 := by
      have he := ε.periodRiemannForm_isAlt.neg_eq y (Complex.I • y)
      rw [hy] at he
      exact neg_eq_zero.mp he
    exact (ε.periodRiemannForm_positive y hne).ne' hz

theorem TypeHodgeStructure.CMEmbeddingType.periodRiemannForm_trace (x y : E) :
    ε.periodRiemannForm (ε.periodEmbedding x) (ε.periodEmbedding y) =
      -(ε.integralPolarization.form x y : ℝ) := by
  rw [ε.integralPolarization_form]
  apply ε.cmPeriodForm_trace
  intro σ
  rw [map_nsmul, Complex.re_nsmul, ε.imaginaryElement_re, smul_zero]

/-- Integrality holds on the constructed discrete lattice, not just an abstract rational model. -/
theorem TypeHodgeStructure.CMEmbeddingType.periodRiemannForm_isInteger (x y : PeriodSpace.CMPeriodSpace E)
    (hx : x ∈ ε.periodIntegerLattice) (hy : y ∈ ε.periodIntegerLattice) :
    ∃ n : ℤ, (n : ℝ) = ε.periodRiemannForm x y := by
  obtain ⟨a, rfl⟩ := (ε.mem_periodIntegerLattice x).mp hx
  obtain ⟨b, rfl⟩ := (ε.mem_periodIntegerLattice y).mp hy
  obtain ⟨n, hn⟩ := ε.integralPolarization_isInteger a b
  refine ⟨-n, ?_⟩
  rw [ε.periodRiemannForm_trace, ← hn]
  push_cast
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CM
