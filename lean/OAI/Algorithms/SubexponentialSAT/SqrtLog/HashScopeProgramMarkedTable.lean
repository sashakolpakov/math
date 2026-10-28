import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramMarkedTableCalls
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramSlots

namespace OAI.Algorithms

/-! Complete physical scope stream, including the optional marked factor.
The final row order is all raw hash rows followed by the marked clause if present. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Complete
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls


theorem appended_scopeWords (t d : ℕ) {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) :
    Marked.appended (clauses := clauses) codes mark
      (Encoding.encodeList id (rows.map (RawTable.scopeBytes (clauses := clauses) t d codes)).reverse)=
      Encoding.encodeList id (scopeWords (clauses := clauses) t d codes rows mark).reverse := by
  cases mark <;> simp [Marked.appended,scopeWords,SubexponentialSAT.Subexp.TupleProgram.prependRecord,Encoding.encodeList]

theorem inputBits_codeRows {m : ℕ} (b : ℕ) (rows : RawTable.Rows m) :
    RawTable.inputBits b rows=Encoding.encodeList (CodeRowsProgram.rowPayload b m) rows := by
  change Encoding.encodeList id (rows.map (CodeRowsProgram.rowPayload b m))=
    Encoding.encodeList (CodeRowsProgram.rowPayload b m) rows
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [Encoding.encodeList,ih]

abbrev command : Cmd 11 80 := .seq initializeCmd (.seq runRows (.seq Marked.optional (.seq seed runReverse)))
def program := compiled command 46 46

def cost (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ) (rows : RawTable.Rows clauses.length)
    (mark : Option (Fin clauses.length)) (index : List Bool) : ℕ :=
  10+RawTable.loopCost t d b modulus clauses codes rows+Marked.optionalCost clauses codes mark index+
    10*(outputBits (clauses := clauses) t d codes rows mark).length

theorem program_runsIn (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : RawTable.Rows clauses.length) (hbound : 3*clauses.length ≤ 2^b)
    (mark : Option (Fin clauses.length)) (index : List Bool)
    (hindex : ∀ i, mark=some i → index=Encoding.encodeNat i.val)
    (width modulus shape : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ rf, RunsIn program (cost t d b modulus clauses codes rows mark index)
      ((data RawTable.zeroRegs width modulus (Encoding.encodeList id clauses) shape
        (RawTable.inputBits b rows) [] index [mark.isSome]).withPC (some program.entry))
      ((data rf width modulus (Encoding.encodeList id clauses) shape (outputBits (clauses := clauses) t d codes rows mark) [] [] []).withPC none) := by
  have hi := initialize_eval width modulus (Encoding.encodeList id clauses) shape (RawTable.inputBits b rows) index [mark.isSome]
  obtain ⟨nr,hnr,rr,hr⟩ := runRows_eval t d ht b hb clauses codes hc rows hbound width modulus shape [false] index [mark.isSome]
    hw hm hshape
  have ha := RawTable.appendScopes_encoded (clauses := clauses) t d codes rows []
  simp only [Encoding.encodeList,List.append_nil] at ha
  rw [ha] at hr
  obtain ⟨nm,hnm,rm,h8,h9,h10,hmark⟩ := Marked.optional_eval clauses codes hc mark index hindex rr width modulus shape
    (Encoding.encodeList id (rows.map (RawTable.scopeBytes (clauses := clauses) t d codes)).reverse)
  rw [appended_scopeWords] at hmark
  have hs := seed_eval rm width modulus (Encoding.encodeList id clauses) shape
    (Encoding.encodeList id (scopeWords (clauses := clauses) t d codes rows mark).reverse) h8
  obtain ⟨nv,hnv,hv⟩ := runReverse_eval rm width modulus (Encoding.encodeList id clauses) shape
    (scopeWords (clauses := clauses) t d codes rows mark).reverse h8 h9 h10
  simp only [List.reverse_reverse] at hv
  have hlen : (Encoding.encodeList id (scopeWords (clauses := clauses) t d codes rows mark).reverse).length=
      (outputBits (clauses := clauses) t d codes rows mark).length := ExecLiteralDedupProgram.encoded_reverse_length _
  rw [hlen] at hnv
  refine ⟨rm,2+(nr+(nm+(2+nv)))+1,by unfold cost; omega,?_⟩
  exact compiled_halt_trace (hi.seq (hr.seq (hmark.seq (hs.seq hv)))) 46 46

theorem primitive_runsIn (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : RawTable.Rows clauses.length) (hbound : 3*clauses.length ≤ 2^b)
    (mark : Option (Fin clauses.length)) (index : List Bool)
    (hindex : ∀ i, mark=some i → index=Encoding.encodeNat i.val)
    (width modulus shape : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * cost t d b modulus clauses codes rows mark index)
      (primitiveCfg program ((data RawTable.zeroRegs width modulus (Encoding.encodeList id clauses) shape
        (RawTable.inputBits b rows) [] index [mark.isSome]).withPC (some program.entry)))
      (primitiveCfg program ((data rf width modulus (Encoding.encodeList id clauses) shape
        (outputBits (clauses := clauses) t d codes rows mark) [] [] []).withPC none)) := by
  obtain ⟨rf,h⟩ := program_runsIn t d ht b hb clauses codes hc rows hbound mark index hindex width modulus shape hw hm hshape
  exact ⟨rf,primitive_execution program h⟩

end SubexponentialSAT.SqrtLog.HashScopeProgram.Complete

end OAI.Algorithms
