import OAI.AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-! # Imaginary Element -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CM

noncomputable section

/-!
# An imaginary field element with the signs of a CM type

Weak approximation at the infinite places produces an element whose
imaginary parts are positive at exactly the embeddings selected by the
CM type. Subtracting its CM conjugate makes it totally imaginary while
retaining those signs. This supplies the field element needed for the
trace Riemann form in the CM realization construction.
-/

open scoped Classical

open _root_.NumberField

variable (E : Type*) [Field E] [Algebra ℚ E]

variable {E} (ε : TypeHodgeStructure.CMEmbeddingType E)

/-- Choose the positive-type embedding above each infinite place. -/
def TypeHodgeStructure.CMEmbeddingType.placeEmbedding (v : InfinitePlace E) : E →ₐ[ℚ] ℂ :=
  if ε.val v.embedding.toRatAlgHom then v.embedding.toRatAlgHom
  else EmbeddingHodgeType.CM.conjugateEmbedding v.embedding.toRatAlgHom

theorem TypeHodgeStructure.CMEmbeddingType.placeEmbedding_positive (v : InfinitePlace E) : ε.val (ε.placeEmbedding v) = true := by
  by_cases hv : ε.val v.embedding.toRatAlgHom = true
  · simp only [TypeHodgeStructure.CMEmbeddingType.placeEmbedding, hv, ↓reduceIte]
  · have hf : ε.val v.embedding.toRatAlgHom = false := Bool.eq_false_iff.mpr hv
    simp only [TypeHodgeStructure.CMEmbeddingType.placeEmbedding, hf, Bool.false_eq_true, ↓reduceIte, ε.property, Bool.not_false]

/-- The chosen embedding still defines the original infinite place. -/
theorem TypeHodgeStructure.CMEmbeddingType.mk_placeEmbedding (v : InfinitePlace E) :
    InfinitePlace.mk (ε.placeEmbedding v).toRingHom = v := by
  by_cases hv : ε.val v.embedding.toRatAlgHom = true
  · simp only [TypeHodgeStructure.CMEmbeddingType.placeEmbedding, hv, ↓reduceIte]
    exact InfinitePlace.mk_embedding v
  · have hf : ε.val v.embedding.toRatAlgHom = false := Bool.eq_false_iff.mpr hv
    simp only [TypeHodgeStructure.CMEmbeddingType.placeEmbedding, hf, Bool.false_eq_true, ↓reduceIte]
    change InfinitePlace.mk (ComplexEmbedding.conjugate v.embedding) = v
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

theorem TypeHodgeStructure.CMEmbeddingType.norm_placeEmbedding (v : InfinitePlace E) (x : E) :
    ‖ε.placeEmbedding v x‖ = v x := by
  change InfinitePlace.mk (ε.placeEmbedding v).toRingHom x = v x
  rw [ε.mk_placeEmbedding]

/-- Continuity in the topology of the corresponding infinite place. -/
theorem TypeHodgeStructure.CMEmbeddingType.placeEmbedding_isometry (v : InfinitePlace E) :
    Isometry ((ε.placeEmbedding v).toRingHom.comp (WithAbs.equiv v.1).toRingHom) :=
  AddMonoidHomClass.isometry_of_norm _ (fun x => by
    change ‖ε.placeEmbedding v (WithAbs.equiv v.1 x)‖ = v (WithAbs.equiv v.1 x)
    exact ε.norm_placeEmbedding v (WithAbs.equiv v.1 x))

/-- At a positively selected embedding, choosing its infinite place recovers that embedding. -/
theorem TypeHodgeStructure.CMEmbeddingType.placeEmbedding_mk (σ : E →ₐ[ℚ] ℂ) (hσ : ε.val σ = true) :
    ε.placeEmbedding (InfinitePlace.mk σ.toRingHom) = σ := by
  obtain he | he := InfinitePlace.embedding_mk_eq σ.toRingHom
  · have ha := congrArg RingHom.toRatAlgHom he
    change (InfinitePlace.mk σ.toRingHom).embedding.toRatAlgHom = σ at ha
    simp only [TypeHodgeStructure.CMEmbeddingType.placeEmbedding, ha, hσ, ↓reduceIte]
  · have ha := congrArg RingHom.toRatAlgHom he
    change (InfinitePlace.mk σ.toRingHom).embedding.toRatAlgHom = EmbeddingHodgeType.CM.conjugateEmbedding σ at ha
    simp only [TypeHodgeStructure.CMEmbeddingType.placeEmbedding, ha, ε.property, hσ, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, EmbeddingHodgeType.CM.conjugateEmbedding_involutive]

variable [NumberField E] [NumberField.IsCMField E]

/-- A nonreal embedding takes some field element to the upper half-plane. -/
theorem TypeHodgeStructure.CMEmbeddingType.exists_positive_im (σ : E →ₐ[ℚ] ℂ) : ∃ x : E, 0 < (σ x).im := by
  have hex : ∃ x : E, (σ x).im ≠ 0 := by
    by_contra! hn
    apply IsTotallyComplex.complexEmbedding_not_isReal σ.toRingHom
    apply ComplexEmbedding.isReal_iff.mpr
    ext x
    apply Complex.ext
    · simp
    · simp [hn x]
  obtain ⟨x, hx⟩ := hex
  rcases lt_or_gt_of_ne hx with hx | hx
  · refine ⟨-x, ?_⟩
    simpa only [map_neg, Complex.neg_im] using neg_pos.mpr hx
  · exact ⟨x, hx⟩

/-- Weak approximation simultaneously makes all selected imaginary parts positive. -/
theorem TypeHodgeStructure.CMEmbeddingType.exists_positive_im_all : ∃ x : E, ∀ σ : E →ₐ[ℚ] ℂ,
    ε.val σ = true → 0 < (σ x).im := by
  let O : Set ((v : InfinitePlace E) → WithAbs v.1) :=
    {x | ∀ v, 0 < (ε.placeEmbedding v (WithAbs.equiv v.1 (x v))).im}
  have ho : IsOpen O := by
    dsimp only [O]
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro v
    exact isOpen_lt continuous_const
      (Complex.continuous_im.comp ((ε.placeEmbedding_isometry v).continuous.comp (continuous_apply v)))
  have hn : O.Nonempty := by
    choose a ha using (fun v : InfinitePlace E => TypeHodgeStructure.CMEmbeddingType.exists_positive_im (ε.placeEmbedding v))
    refine ⟨fun v => (WithAbs.equiv v.1).symm (a v), ?_⟩
    intro v
    simpa only [RingEquiv.apply_symm_apply] using ha v
  obtain ⟨x, hx⟩ := (InfinitePlace.denseRange_algebraMap_pi E).exists_mem_open ho hn
  refine ⟨x, ?_⟩
  intro σ hσ
  have hv := hx (InfinitePlace.mk σ.toRingHom)
  rw [ε.placeEmbedding_mk σ hσ] at hv
  exact hv

/-- The totally imaginary element required for the trace Riemann form exists for every CM type. -/
theorem TypeHodgeStructure.CMEmbeddingType.exists_imaginaryElement : ∃ ξ : E,
    NumberField.IsCMField.complexConj E ξ = -ξ ∧
      ∀ σ : E →ₐ[ℚ] ℂ, ε.val σ = true → 0 < (σ ξ).im := by
  obtain ⟨x, hx⟩ := ε.exists_positive_im_all
  refine ⟨x - NumberField.IsCMField.complexConj E x, ?_, ?_⟩
  · simp only [map_sub, NumberField.IsCMField.complexConj_apply_apply, neg_sub]
  · intro σ hσ
    have hp := hx σ hσ
    have hc : σ (NumberField.IsCMField.complexConj E x) = (starRingEnd ℂ) (σ x) :=
      NumberField.IsCMField.complexEmbedding_complexConj E σ.toRingHom x
    rw [map_sub, Complex.sub_im, hc, Complex.conj_im]
    linarith

/-- A chosen totally imaginary element with the embedding signs of this CM type. -/
def TypeHodgeStructure.CMEmbeddingType.imaginaryElement : E := ε.exists_imaginaryElement.choose

theorem TypeHodgeStructure.CMEmbeddingType.imaginaryElement_conjugate :
    NumberField.IsCMField.complexConj E ε.imaginaryElement = -ε.imaginaryElement :=
  ε.exists_imaginaryElement.choose_spec.1

theorem TypeHodgeStructure.CMEmbeddingType.imaginaryElement_positive (σ : E →ₐ[ℚ] ℂ) (hσ : ε.val σ = true) :
    0 < (σ ε.imaginaryElement).im := ε.exists_imaginaryElement.choose_spec.2 σ hσ

theorem TypeHodgeStructure.CMEmbeddingType.imaginaryElement_negative (σ : E →ₐ[ℚ] ℂ) (hσ : ε.val σ = false) :
    (σ ε.imaginaryElement).im < 0 := by
  have hp := ε.imaginaryElement_positive (EmbeddingHodgeType.CM.conjugateEmbedding σ)
    (by rw [ε.property, hσ]; rfl)
  change 0 < ((starRingEnd ℂ) (σ ε.imaginaryElement)).im at hp
  rw [Complex.conj_im] at hp
  exact neg_pos.mp hp

theorem TypeHodgeStructure.CMEmbeddingType.imaginaryElement_ne_zero : ε.imaginaryElement ≠ 0 := by
  let v : InfinitePlace E := Classical.choice inferInstance
  have hp := ε.imaginaryElement_positive (ε.placeEmbedding v) (ε.placeEmbedding_positive v)
  intro hz
  simp [hz] at hp

theorem TypeHodgeStructure.CMEmbeddingType.imaginaryElement_re (σ : E →ₐ[ℚ] ℂ) : (σ ε.imaginaryElement).re = 0 := by
  have hc : (starRingEnd ℂ) (σ ε.imaginaryElement) = -σ ε.imaginaryElement := by
    calc
      (starRingEnd ℂ) (σ ε.imaginaryElement) =
          σ (NumberField.IsCMField.complexConj E ε.imaginaryElement) :=
        (NumberField.IsCMField.complexEmbedding_complexConj E σ.toRingHom ε.imaginaryElement).symm
      _ = -σ ε.imaginaryElement := by rw [ε.imaginaryElement_conjugate, map_neg]
  have hr := congrArg Complex.re hc
  simp only [Complex.conj_re, Complex.neg_re] at hr
  linarith

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CM
