import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingLieIndices
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.BaseChange

/-! # Embedding Ranks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Specializing the original geometric rank condition computes the
Lie rank at every selected complex embedding on every complex fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [IsGalois ℚ E] [Field K] [NumberField K]
    {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))} (A : PEL.Objects.PELObject P iota N T)
    (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ) (p : Spec (.of ℂ) ⟶ T.left)
    (hp : p ≫ T.hom = Spec.map (CommRingCat.ofHom κ))

include hκ hp in
omit [NumberField K] in
theorem PEL.Objects.PELObject.complexFiber_embedding_rank (hP : P.IsAdmissible) (i : Fin s) :
    LieRanks.HasLieRank (A.polarized.abelian.pullback p) (A.action.pullback p)
      ((P.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E))
      (P.firstLieRank i) := by
  obtain ⟨τ, hτ⟩ := EmbeddingLieIndices.embedding_eq_comp_aut (P.embeddings P.distinguished) (P.embeddings i)
  have hr := A.lieRanks ℂ κ p hp τ
  have he : ((κ.comp iota).comp (τ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E))) =
      (P.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E) := by
    rw [hκ, ← RingHom.comp_assoc]
    exact congrArg (fun f : E →+* ℂ => f.comp (algebraMap (NumberField.RingOfIntegers E) E)) hτ
  rw [he, P.lieRank_of_embedding hP τ i hτ] at hr
  exact hr

include hκ hp in
omit [NumberField K] in
theorem PEL.Objects.PELObject.complexFiber_distinguished_rank (hP : P.IsAdmissible) :
    LieRanks.HasLieRank (A.polarized.abelian.pullback p) (A.action.pullback p)
      (P.μ.comp (algebraMap (NumberField.RingOfIntegers E) E)) 2 := by
  have hr := A.complexFiber_embedding_rank κ hκ p hp hP P.distinguished
  have he : P.firstLieRank P.distinguished = 2 := ite_eq_left rfl
  rw [he] at hr
  exact hr

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
