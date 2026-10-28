import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramNativeSemantics

namespace OAI.Algorithms

/-! Scope extraction can run before the eventual coefficient ring is selected.
A fixed two-bit temporary scalar shape gives exactly the same scope stream. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram

theorem interpreted_scope_independent (t d t' d' : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (row : List (Fin clauses.length × ZMod 3)) :
    scope (FromTuple.interpretedTerms (clauses := clauses) t d codes row)=
      scope (FromTuple.interpretedTerms (clauses := clauses) t' d' codes row) := by
  simp [scope,mergedCodes,FromTuple.interpretedTerms,List.flatMap_map,← List.map_reverse]

namespace Complete

theorem scopes_independent (t d t' d' : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (rows : RawTable.Rows clauses.length)
    (mark : Option (Fin clauses.length)) :
    scopes (clauses := clauses) t d codes rows mark=scopes (clauses := clauses) t' d' codes rows mark := by
  unfold scopes
  congr 1
  apply List.map_congr_left
  intro row _
  exact interpreted_scope_independent t d t' d' codes row

theorem outputBits_independent (t d t' d' : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (rows : RawTable.Rows clauses.length)
    (mark : Option (Fin clauses.length)) :
    outputBits (clauses := clauses) t d codes rows mark=outputBits (clauses := clauses) t' d' codes rows mark := by
  rw [outputBits_nested,outputBits_nested,scopes_independent t d t' d' codes rows mark]

@[simp] theorem scopeOnly_shape :
    ([false,false] : List Bool).length=(0+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 1 := by
  have hlog : Nat.log 2 3=1 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  simp [SubexponentialSAT.SubexpLiftRing.baseWidth,hlog]

end Complete
end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
