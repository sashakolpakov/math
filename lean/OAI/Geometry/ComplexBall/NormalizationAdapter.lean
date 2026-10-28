import OAI.Geometry.ComplexBall.Intrinsic
import OAI.Geometry.ComplexBall.ArithmeticQuotientOf

/-! # Normalization Adapter -/

namespace OAI.Geometry.ComplexBall.NormalizationAdapter.PrescribedSigns.Intrinsic

noncomputable section

section

open scoped Classical

variable {E Place : Type*} [Field E] [CharZero E]

def adaptedMatrix (b : E) : Matrix (Fin 3) (Fin 3) E := Matrix.diagonal ![1, 1, b]

lemma adaptedMatrix_hermitian [NumberField E] [NumberField.IsCMField E] (b : E)
    (hb : NumberField.IsCMField.complexConj E b = b) :
    ∀ j k, adaptedMatrix b j k = NumberField.IsCMField.complexConj E (adaptedMatrix b k j) := by
  intro j k
  fin_cases j <;> fin_cases k <;> simp [adaptedMatrix, Matrix.diagonal, hb]

lemma adaptedMatrix_local (σ : Place → E →ₐ[ℚ] ℂ) (τ : Place) (b : E) (x y : PrescribedSignsB.Vec) :
    PrescribedSignsB.localB σ (adaptedMatrix b) τ x y = x 0 * y 0 + x 1 * y 1 + x 2 * σ τ b * y 2 := by
  simp [PrescribedSignsB.localB, adaptedMatrix, Fin.sum_univ_succ, Matrix.diagonal, add_assoc]

lemma adaptedMatrix_real (σ : Place → E →ₐ[ℚ] ℂ) (τ : Place) (b : E) (x : PrescribedSignsB.Vec) :
    (PrescribedSignsB.localB σ (adaptedMatrix b) τ x (star x)).re =
      Complex.normSq (x 0) + Complex.normSq (x 1) + (σ τ b).re * Complex.normSq (x 2) := by
  rw [adaptedMatrix_local]
  simp only [Pi.star_apply, Complex.add_re, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.mul_im, Complex.normSq_apply]
  ring

lemma adaptedMatrix_active_positive (σ : Place → E →ₐ[ℚ] ℂ) (μ : Place) (b : E) :
    ∀ x : PrescribedSignsB.Vec, x ≠ 0 → x 2 = 0 → 0 < (PrescribedSignsB.localB σ (adaptedMatrix b) μ x (star x)).re := by
  intro x hx hx2
  rw [adaptedMatrix_real, hx2, Complex.normSq_zero, mul_zero, add_zero]
  have h0 := Complex.normSq_nonneg (x 0)
  have h1 := Complex.normSq_nonneg (x 1)
  by_contra hn
  have hz0 : x 0 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have hz1 : x 1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  apply hx
  ext j
  fin_cases j <;> assumption

lemma adaptedMatrix_positive (σ : Place → E →ₐ[ℚ] ℂ) (τ : Place) (b : E)
    (hb : 0 < (σ τ b).re) :
    ∀ x : PrescribedSignsB.Vec, x ≠ 0 → 0 < (PrescribedSignsB.localB σ (adaptedMatrix b) τ x (star x)).re := by
  intro x hx
  rw [adaptedMatrix_real]
  have h0 := Complex.normSq_nonneg (x 0)
  have h1 := Complex.normSq_nonneg (x 1)
  have h2 := Complex.normSq_nonneg (x 2)
  by_contra hn
  have hz2 : x 2 = 0 := Complex.normSq_eq_zero.mp (by nlinarith)
  have hz0 : x 0 = 0 := Complex.normSq_eq_zero.mp (by nlinarith)
  have hz1 : x 1 = 0 := Complex.normSq_eq_zero.mp (by nlinarith)
  apply hx
  ext j
  fin_cases j <;> assumption

/-- The actual scalar produced by unconditional ArithmeticQuotient gives the adapted
matrix hypotheses used by the full PrescribedSigns theorem. -/
lemma adaptedMatrix_from_ArithmeticQuotient [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1)) (μ : Place)
    (hother : ∃ ν : E →+* ℂ, ν ≠ (σ μ).toRingHom ∧
      ν ≠ (starRingEnd ℂ).comp (σ μ).toRingHom) :
    ∃ b : E, b ≠ 0 ∧ NumberField.IsCMField.complexConj E b = b ∧
      (∀ j k, adaptedMatrix b j k =
        NumberField.IsCMField.complexConj E (adaptedMatrix b k j)) ∧
      (∀ x : PrescribedSignsB.Vec, x ≠ 0 → x 2 = 0 →
        0 < (PrescribedSignsB.localB σ (adaptedMatrix b) μ x (star x)).re) ∧
      (PrescribedSignsB.localB σ (adaptedMatrix b) μ ![0,0,1] ![0,0,1]).re < 0 ∧
      (∀ τ, τ ≠ μ → ∀ x : PrescribedSignsB.Vec, x ≠ 0 →
        0 < (PrescribedSignsB.localB σ (adaptedMatrix b) τ x (star x)).re) := by
  obtain ⟨b, hbc, hb, hbμ, hbτ, _⟩ :=
    ArithmeticQuotientOf.existence_of_compact_ball_quotients (σ μ).toRingHom hother
  refine ⟨b, hb, hbc, adaptedMatrix_hermitian b hbc,
    adaptedMatrix_active_positive σ μ b, ?_, ?_⟩
  · simpa [adaptedMatrix_local] using hbμ
  · intro τ hτ
    apply adaptedMatrix_positive σ τ b
    apply hbτ (σ τ).toRingHom
    · intro he
      have he' : σ τ = σ μ := AlgHom.ext (fun x => DFunLike.congr_fun he x)
      have hp : (τ, false) = (μ, false) := hσ.injective (by simpa using he')
      exact hτ (congrArg Prod.fst hp)
    · intro he
      have he' : σ τ = AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ μ) := AlgHom.ext (fun x => DFunLike.congr_fun he x)
      have hp : (τ, false) = (μ, true) := hσ.injective (by simpa using he')
      exact Bool.false_ne_true (congrArg Prod.snd hp)

end

open scoped Classical

def normalizedConjugation (E : IntermediateField ℚ ℂ)
    [NumberField E] [NumberField.IsCMField E] : Gal(E/ℚ) :=
  (NumberField.IsCMField.complexConj E).restrictScalars ℚ

def normalizedEmbeddingEquiv (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] : Gal(E/ℚ) ≃ (E →ₐ[ℚ] ℂ) :=
  (Normal.algHomEquivAut ℚ ℂ E).symm

lemma normalizedEmbeddingEquiv_conjugation (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E] (g : Gal(E/ℚ)) :
    normalizedEmbeddingEquiv E (normalizedConjugation E * g) =
      AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (normalizedEmbeddingEquiv E g) := by
  ext x
  exact NumberField.IsCMField.complexEmbedding_complexConj E E.val.toRingHom (g x)

/-- Representatives supplied by the active branch of geometric LefschetzNormalization
index the actual conjugate pairs of embeddings required by PrescribedSigns. -/
lemma normalized_representatives (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (reps : Finset (Gal(E/ℚ)))
    (hr : ∀ τ, τ ∈ reps ↔ normalizedConjugation E * τ ∉ reps) :
    Function.Bijective (fun p : {τ // τ ∈ reps} × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (normalizedEmbeddingEquiv E p.1.val)
      else normalizedEmbeddingEquiv E p.1.val) := by
  have hinv (τ : Gal(E/ℚ)) : normalizedConjugation E * (normalizedConjugation E * τ) = τ := by
    ext x
    exact congrArg Subtype.val (NumberField.IsCMField.complexConj_apply_apply E (τ x))
  have hd (τ : {τ // τ ∈ reps}) : normalizedConjugation E * τ.val ∉ reps := (hr τ.val).mp τ.property
  constructor
  · rintro ⟨⟨τ, hτ⟩, b⟩ ⟨⟨υ, hυ⟩, c⟩ he
    cases b <;> cases c
    · simp only [Bool.false_eq_true, ↓reduceIte] at he
      exact congrArg (fun t : {τ // τ ∈ reps} => (t, false))
        (Subtype.ext ((normalizedEmbeddingEquiv E).injective he))
    · simp only [Bool.false_eq_true, ↓reduceIte] at he
      rw [← normalizedEmbeddingEquiv_conjugation] at he
      exact False.elim (hd ⟨υ, hυ⟩ ((normalizedEmbeddingEquiv E).injective he ▸ hτ))
    · simp only [Bool.false_eq_true, ↓reduceIte] at he
      rw [← normalizedEmbeddingEquiv_conjugation] at he
      exact False.elim (hd ⟨τ, hτ⟩ ((normalizedEmbeddingEquiv E).injective he ▸ hυ))
    · simp only [↓reduceIte] at he
      rw [← normalizedEmbeddingEquiv_conjugation, ← normalizedEmbeddingEquiv_conjugation] at he
      exact congrArg (fun t : {τ // τ ∈ reps} => (t, true))
        (Subtype.ext (mul_left_cancel ((normalizedEmbeddingEquiv E).injective he)))
  · intro σ
    obtain ⟨τ, rfl⟩ := (normalizedEmbeddingEquiv E).surjective σ
    by_cases hτ : τ ∈ reps
    · exact ⟨(⟨τ, hτ⟩, false), rfl⟩
    · have hc : normalizedConjugation E * τ ∈ reps := (hr _).mpr (by simpa only [hinv] using hτ)
      refine ⟨(⟨normalizedConjugation E * τ, hc⟩, true), ?_⟩
      simpa only [↓reduceIte, hinv] using (normalizedEmbeddingEquiv_conjugation E (normalizedConjugation E * τ)).symm

/-- The inverse Galois index in LefschetzNormalization's normalized sign tuple is retained
when restricting its first two entries to the chosen representatives. -/
def normalizedSigns {G : Type*} [Group G] (w : Fin 4 → G → Bool)
    (reps : Finset G) : Fin 2 → {τ // τ ∈ reps} → Bool :=
  fun i τ => w (Fin.castLE (by decide) i) τ.val⁻¹

lemma normalizedSigns_agree {G : Type*} [Group G]
    (w d : Fin 4 → G → Bool) (reps : Finset G)
    (hd : ∀ i τ, d i τ = w i τ⁻¹) (i : Fin 2) (τ : {τ // τ ∈ reps}) :
    normalizedSigns w reps i τ = d (Fin.castLE (by decide) i) τ.val :=
  (hd _ _).symm

lemma normalized_active_embedding (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E]
    (reps : Finset (Gal(E/ℚ))) (h1 : (1 : Gal(E/ℚ)) ∈ reps) :
    normalizedEmbeddingEquiv E (⟨1, h1⟩ : {τ // τ ∈ reps}).val = E.val := rfl

lemma normalizedSigns_active {G : Type*} [Group G]
    (w : Fin 4 → G → Bool) (reps : Finset G) (h1 : (1 : G) ∈ reps)
    (hw : ∀ i, w i 1 = true) (i : Fin 2) :
    normalizedSigns w reps i ⟨1, h1⟩ = true := by
  simpa only [normalizedSigns, inv_one] using hw (Fin.castLE (by decide) i)

end

end OAI.Geometry.ComplexBall.NormalizationAdapter.PrescribedSigns.Intrinsic
