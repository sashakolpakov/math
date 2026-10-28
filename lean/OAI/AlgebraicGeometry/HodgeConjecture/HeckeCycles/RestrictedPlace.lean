import OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPadic

/-! # Restricted Place -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedPlace.CM

noncomputable section

/-! Restrict the actual chosen arithmetic place to the original field.
The algebraic-closure embeddings are retained, and the integral local
characters and all residue coordinates agree under the field inclusion. -/

open _root_.NumberField
open OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPadic

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  {κ : K →+* ℂ} {κL : L →+* ℂ} (i : K →+* L) (hi : κL.comp i = κ)
  {q : ℕ} [Fact q.Prime] (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κL q)

abbrev fieldEmbedding : K →+* Padic q :=
  (j.completion.toRingHom.comp (FinitePlace.embedding j.prime)).comp i

def choice : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q where
  complexClosure := j.complexClosure
  fieldInClosure := j.fieldInClosure.comp i
  complex_compatibility := by
    rw [← RingHom.comp_assoc, j.complex_compatibility]
    exact hi
  iota := j.iota
  prime := PELModuli.CMPoints.LocalPadic.embeddingPlace (fieldEmbedding i j)
  liesOver := PELModuli.CMPoints.LocalPadic.embeddingPlace_liesOver (fieldEmbedding i j)
  completion := PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv (fieldEmbedding i j)
  completion_continuous := PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_continuous (fieldEmbedding i j)
  completion_inverse_continuous := PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_symm_continuous (fieldEmbedding i j)
  closure_compatibility := by
    rw [PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_comp, ← RingHom.comp_assoc, j.closure_compatibility]
    rfl
  integralEmbedding := j.integralEmbedding.comp (RingOfIntegers.mapRingHom i)
  integral_compatibility := by
    rw [PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_comp, ← RingHom.comp_assoc, j.integral_compatibility]
    ext a
    rfl

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] (e : E →+* K)

theorem localCharacter_eq (τ : Gal(E/ℚ)) :
    (choice i hi j).localCharacter e τ = j.localCharacter (i.comp e) τ := by
  ext a
  rfl

theorem residueCharacter_eq (τ : Gal(E/ℚ)) (n : ℕ) :
    (choice i hi j).residueCharacter e τ n = j.residueCharacter (i.comp e) τ n := by
  unfold PELModuli.CMPoints.Arithmetic.QadicChoice.residueCharacter
  rw [localCharacter_eq]

theorem residueCoordinates_eq (n : ℕ) :
    (choice i hi j).residueCoordinates e n = j.residueCoordinates (i.comp e) n := by
  ext a τ
  exact RingHom.congr_fun (residueCharacter_eq i hi j e τ n) a

theorem splitCoordinates (hsplit : j.HasSplitCoordinates (i.comp e)) :
    (choice i hi j).HasSplitCoordinates e := by
  intro n
  rw [residueCoordinates_eq]
  exact hsplit n

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedPlace.CM
