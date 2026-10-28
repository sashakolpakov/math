import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.EmbeddingRanks
import Mathlib.Data.Fintype.BigOperators

/-! # Lie Ranks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The actual CM embedding enumeration gives all prescribed Lie ranks,
including the conjugate ranks, and their sum is the abelian dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s)

section

def Datum.RankThreePELDatum.pairedEmbedding (p : Fin s × Bool) : E →ₐ[ℚ] ℂ :=
  if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings p.1) else P.embeddings p.1

def Datum.RankThreePELDatum.pairedLieRank (p : Fin s × Bool) : ℕ :=
  if p.2 then 3 - P.firstLieRank p.1 else P.firstLieRank p.1

theorem Datum.RankThreePELDatum.pairedEmbedding_injective (hP : P.IsAdmissible) :
    Function.Injective P.pairedEmbedding := hP.1.1

omit [NumberField E] [NumberField.IsCMField E] in
theorem Datum.RankThreePELDatum.firstLieRank_le_three (i : Fin s) : P.firstLieRank i ≤ 3 := by
  unfold Datum.RankThreePELDatum.firstLieRank
  split_ifs <;> decide

omit [NumberField E] [NumberField.IsCMField E] in
theorem Datum.RankThreePELDatum.pairedLieRank_sum : (∑ p : Fin s × Bool, P.pairedLieRank p) = 3 * s := by
  classical
  rw [Fintype.sum_prod_type]
  have hi (i : Fin s) : (∑ b : Bool, P.pairedLieRank (i, b)) = 3 := by
    simp only [Fintype.sum_bool]
    change (3 - P.firstLieRank i) + P.firstLieRank i = 3
    exact Nat.sub_add_cancel (P.firstLieRank_le_three i)
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.mul_comm s 3

theorem Datum.RankThreePELDatum.lieRank_of_pairedEmbedding (hP : P.IsAdmissible) (τ : E ≃ₐ[ℚ] E)
    (p : Fin s × Bool) (hτ : P.μ.comp τ.toRingHom = (P.pairedEmbedding p).toRingHom) :
    P.lieRank τ = P.pairedLieRank p := by
  classical
  have heq (q : Fin s × Bool) :
      (P.pairedEmbedding p).toRingHom = (P.pairedEmbedding q).toRingHom ↔ p = q := by
    constructor
    · intro h
      exact P.pairedEmbedding_injective hP (AlgHom.ext
        (fun x => congrArg (fun f : E →+* ℂ => f x) h))
    · rintro rfl
      rfl
  unfold Datum.RankThreePELDatum.lieRank
  rw [hτ]
  change (∑ i : Fin s,
    if (P.pairedEmbedding p).toRingHom = (P.pairedEmbedding (i, false)).toRingHom
      then P.firstLieRank i
    else if (P.pairedEmbedding p).toRingHom = (P.pairedEmbedding (i, true)).toRingHom
      then 3 - P.firstLieRank i else 0) = P.pairedLieRank p
  simp only [heq]
  rcases p with ⟨i, b⟩
  cases b <;> simp [Datum.RankThreePELDatum.pairedLieRank]

end

variable [IsGalois ℚ E] {K : Type} [Field K] [NumberField K]
    {N : ℕ} {iota : E →+* K} {T : Over (Spec (.of K))}
    (A : PEL.Objects.PELObject P iota N T) (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ)
    (p : Spec (.of ℂ) ⟶ T.left) (hp : p ≫ T.hom = Spec.map (CommRingCat.ofHom κ))

include hκ hp in
omit [NumberField K] in
theorem PEL.Objects.PELObject.complexFiber_paired_rank (hP : P.IsAdmissible) (j : Fin s × Bool) :
    LieRanks.HasLieRank (A.polarized.abelian.pullback p) (A.action.pullback p)
      ((P.pairedEmbedding j).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E))
      (P.pairedLieRank j) := by
  obtain ⟨τ, hτ⟩ := EmbeddingLieIndices.embedding_eq_comp_aut (P.embeddings P.distinguished) (P.pairedEmbedding j)
  have hr := A.lieRanks ℂ κ p hp τ
  have he : ((κ.comp iota).comp (τ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E))) =
      (P.pairedEmbedding j).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E) := by
    rw [hκ, ← RingHom.comp_assoc]
    exact congrArg (fun f : E →+* ℂ => f.comp (algebraMap (NumberField.RingOfIntegers E) E)) hτ
  rw [he, P.lieRank_of_pairedEmbedding hP τ j hτ] at hr
  exact hr

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
