import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects
import Mathlib.FieldTheory.Galois.Basic

/-! # Embedding Lie Indices -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The Galois-indexed rank condition gives the declared rank at each
actual embedding, with the conjugate embeddings distinguished explicitly. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s)

omit [NumberField E] [NumberField.IsCMField E] in
theorem EmbeddingLieIndices.embedding_eq_comp_aut [IsGalois ℚ E] (μ σ : E →ₐ[ℚ] ℂ) :
    ∃ τ : E ≃ₐ[ℚ] E, μ.toRingHom.comp τ.toRingHom = σ.toRingHom := by
  let : Algebra E ℂ := μ.toAlgebra
  let : IsScalarTower ℚ E ℂ := IsScalarTower.of_algebraMap_eq' μ.comp_algebraMap.symm
  let e := Normal.algHomEquivAut ℚ ℂ E
  refine ⟨e σ, ?_⟩
  exact congrArg AlgHom.toRingHom (e.symm_apply_apply σ)

theorem Datum.RankThreePELDatum.embeddings_injective (hP : P.IsAdmissible) : Function.Injective P.embeddings := by
  intro i j hij
  have h := @hP.1.1 (i, false) (j, false) hij
  exact congrArg Prod.fst h

theorem Datum.RankThreePELDatum.embedding_ne_conjugate (hP : P.IsAdmissible) (i j : Fin s) :
    (P.embeddings i).toRingHom ≠ (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings j)).toRingHom := by
  intro he
  have h := @hP.1.1 (i, false) (j, true) (AlgHom.ext
    (fun x => congrArg (fun f : E →+* ℂ => f x) he))
  have hf : false = true := congrArg Prod.snd h
  cases hf

theorem Datum.RankThreePELDatum.lieRank_of_embedding (hP : P.IsAdmissible) (τ : E ≃ₐ[ℚ] E) (i : Fin s)
    (hτ : P.μ.comp τ.toRingHom = (P.embeddings i).toRingHom) :
    P.lieRank τ = P.firstLieRank i := by
  classical
  unfold Datum.RankThreePELDatum.lieRank
  rw [hτ]
  have heq (j : Fin s) : (P.embeddings i).toRingHom = (P.embeddings j).toRingHom ↔ i = j := by
    constructor
    · intro h
      exact P.embeddings_injective hP (AlgHom.ext (fun x => congrArg (fun f : E →+* ℂ => f x) h))
    · rintro rfl
      rfl
  simp only [heq, P.embedding_ne_conjugate hP, ite_false]
  simp

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
