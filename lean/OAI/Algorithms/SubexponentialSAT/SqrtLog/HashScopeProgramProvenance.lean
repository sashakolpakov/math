import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramRawScope

namespace OAI.Algorithms

/-! Exact serialization bridges for the native scope-table output. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram

theorem scopeBits_nested (rows : Outer.Rows) :
    Outer.scopeBits rows = Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (rows.map scope) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simpa [Outer.scopeBits,Outer.scopeBytes,Encoding.encodeList] using congrArg
        (fun rest => true :: (Encoding.frame (Outer.scopeBytes row) ++ rest)) ih

theorem inputBits_raw {n m depth : ℕ} (weight : ZMod 3 → Word)
    (source : Fin m → List (SAT.Literal (Fin n))) (hs : List (HashFamily.Candidate m depth)) :
    Outer.inputBits (hs.map (rawTerms weight source)) =
      Encoding.encodeList (fun h => Encoding.encodeList id
        ((HashInputProgram.rawRow source h).map fun term =>
          HashInputProgram.weightedPayload (weight term.1) term.2)) hs := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
      simp only [Outer.inputBits,List.map_cons,Encoding.encodeList]
      congr 1
      simp only [Outer.inputBits] at ih
      rw [ih]
      congr 1
      unfold Outer.rowBits
      have hm := rawTerms_payload weight source h
      have hf (terms : List Term) : Encoding.encodeList payload terms = Encoding.encodeList id (terms.map payload) := by
        induction terms with
        | nil => rfl
        | cons t ts iht => simp [Encoding.encodeList,iht]
      rw [hf,hm]
      rfl


end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
