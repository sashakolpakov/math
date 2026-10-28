import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramFrontendInputBounds

namespace OAI.Algorithms

/-! Physical length bounds for the six paid serialization operations. The
input length vector remains explicit; no arbitrary padding bound is assumed. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

open Circuit
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem lengths (m : Model) (j : Fin 64) :
    (result code m).len j =
      if j=44 then m.len 35 else if j=45 then m.len 33+m.len 33+1 else m.len j := by
  by_cases h44 : j=44
  · subst j
    simp [code,result,next,output,lengthBound]
  · by_cases h45 : j=45
    · subst j
      simp [code,result,next,output,lengthBound]
    · simp [code,result,next,output,lengthBound,h44,h45]

theorem lengths_le (m : Model) (B : ℕ) (hm : ∀ j,m.len j ≤ B) (j : Fin 64) :
    (result code m).len j ≤ 2*B+1 := by
  rw [lengths]
  split_ifs <;> have h33 := hm 33 <;> have h35 := hm 35 <;> have hj := hm j <;> omega

/-- Applies in particular at the frontend's actual canonical input-length
vector. The bound changes with that vector, rather than quantifying it away. -/
theorem guarded_lengths_le (x : Input) (l : Fin 8 → ℕ) (j : Fin 64) :
    (result code (Execute.guardedModel x l)).len j ≤ 2*Execute.runtimeBound x l+1 :=
  lengths_le _ _ (FrontendBounds.guarded_length_le (x,l)) j

theorem guarded_length_sup_le (x : Input) (l : Fin 8 → ℕ) :
    Finset.univ.sup (result code (Execute.guardedModel x l)).len ≤
      2*Execute.runtimeBound x l+1 := by
  apply Finset.sup_le
  intro j _
  exact guarded_lengths_le x l j

theorem guarded_word_lengths_le (x : Input) (l : Fin 8 → ℕ) (w : Bank.Words)
    (hs : Shape (result code (Execute.guardedModel x l)) w) (j : Fin 64) :
    (w j).length ≤ 2*Execute.runtimeBound x l+1 :=
  (hs.2 j).trans (guarded_lengths_le x l j)

/-- One fixed polynomial bounds every serialized port whenever the eight
actual source values and their chosen physical length caps are bounded. -/
theorem uniform_guarded_lengths_polynomial :
    ∃ C d : ℕ, ∀ (x : Input) (l : Fin 8 → ℕ) (S : ℕ),
      FrontendBounds.CountsBound x S → (∀ i,l i ≤ S) →
      ∀ j, (result code (Execute.guardedModel x l)).len j ≤ C*(S+1)^d := by
  obtain ⟨C,d,h⟩ := FrontendBounds.uniform_polynomial
  refine ⟨2*C+1,d,?_⟩
  intro x l S hv hl j
  have hb := (h x l S hv hl).1
  have hj := guarded_lengths_le x l j
  have hp : 1 ≤ (S+1)^d := one_le_pow₀ (by omega)
  nlinarith

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

#print axioms SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.guarded_lengths_le
#print axioms SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.uniform_guarded_lengths_polynomial

end OAI.Algorithms
