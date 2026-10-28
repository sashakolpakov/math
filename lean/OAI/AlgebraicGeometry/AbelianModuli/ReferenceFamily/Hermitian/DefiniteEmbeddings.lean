import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization

/-! # Definite Embeddings -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Definiteness is preserved by conjugating a complex embedding. The
specified CM embedding enumeration therefore gives definiteness at
every embedding away from the distinguished conjugate pair. -/

variable {E : Type} [Field E]

theorem Hermitian.DefiniteEmbeddings.complexMatrixHermitian_conjugate (μ : E →+* ℂ)
    (H : Matrix (Fin 3) (Fin 3) E) (x y : Fin 3 → ℂ) :
    Datum.RankThreePELDatum.complexMatrixHermitian ((starRingEnd ℂ).comp μ) H x y =
      star (Datum.RankThreePELDatum.complexMatrixHermitian μ H
        (fun i => star (x i)) (fun i => star (y i))) := by
  simp only [Datum.RankThreePELDatum.complexMatrixHermitian, RingHom.comp_apply,
    starRingEnd_apply, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem Hermitian.DefiniteEmbeddings.complexMatrixHermitian_definite_conjugate (μ : E →+* ℂ)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hdef : (∀ x : Fin 3 → ℂ, x ≠ 0 →
      0 < (Datum.RankThreePELDatum.complexMatrixHermitian μ H x x).re) ∨
      (∀ x : Fin 3 → ℂ, x ≠ 0 →
        (Datum.RankThreePELDatum.complexMatrixHermitian μ H x x).re < 0)) :
    (∀ x : Fin 3 → ℂ, x ≠ 0 →
      0 < (Datum.RankThreePELDatum.complexMatrixHermitian ((starRingEnd ℂ).comp μ) H x x).re) ∨
      (∀ x : Fin 3 → ℂ, x ≠ 0 →
        (Datum.RankThreePELDatum.complexMatrixHermitian ((starRingEnd ℂ).comp μ) H x x).re < 0) := by
  have hn (x : Fin 3 → ℂ) (hx : x ≠ 0) : (fun i => star (x i)) ≠ 0 := by
    intro h
    apply hx
    funext i
    simpa only [Pi.zero_apply, star_star, star_zero] using congrArg star (congrFun h i)
  rcases hdef with hp | hm
  · left
    intro x hx
    rw [Hermitian.DefiniteEmbeddings.complexMatrixHermitian_conjugate, Complex.star_def, Complex.conj_re]
    exact hp _ (hn x hx)
  · right
    intro x hx
    rw [Hermitian.DefiniteEmbeddings.complexMatrixHermitian_conjugate, Complex.star_def, Complex.conj_re]
    exact hm _ (hn x hx)

variable [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s)

theorem Datum.RankThreePELDatum.definite_other_embedding (hP : P.IsAdmissible)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hdef : ∀ i, i ≠ P.distinguished →
      (∀ x : Fin 3 → ℂ, x ≠ 0 →
        0 < (Datum.RankThreePELDatum.complexMatrixHermitian (P.embeddings i).toRingHom H x x).re) ∨
      (∀ x : Fin 3 → ℂ, x ≠ 0 →
        (Datum.RankThreePELDatum.complexMatrixHermitian (P.embeddings i).toRingHom H x x).re < 0))
    (ν : E →+* ℂ) (hν : ν ≠ P.μ) (hνc : ν ≠ (starRingEnd ℂ).comp P.μ) :
    (∀ x : Fin 3 → ℂ, x ≠ 0 → 0 < (Datum.RankThreePELDatum.complexMatrixHermitian ν H x x).re) ∨
      (∀ x : Fin 3 → ℂ, x ≠ 0 → (Datum.RankThreePELDatum.complexMatrixHermitian ν H x x).re < 0) := by
  obtain ⟨⟨i, side⟩, hi⟩ := hP.1.2 ν.toRatAlgHom
  cases side
  · have he : (P.embeddings i).toRingHom = ν := congrArg AlgHom.toRingHom hi
    have hne : i ≠ P.distinguished := by
      intro h
      subst i
      exact hν he.symm
    rw [← he]
    exact hdef i hne
  · have he : (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)).toRingHom = ν :=
      congrArg AlgHom.toRingHom hi
    have hne : i ≠ P.distinguished := by
      intro h
      subst i
      exact hνc he.symm
    rw [← he]
    have hc : (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)).toRingHom =
        (starRingEnd ℂ).comp (P.embeddings i).toRingHom := by
      ext x
      rfl
    rw [hc]
    exact Hermitian.DefiniteEmbeddings.complexMatrixHermitian_definite_conjugate (P.embeddings i).toRingHom H (hdef i hne)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
