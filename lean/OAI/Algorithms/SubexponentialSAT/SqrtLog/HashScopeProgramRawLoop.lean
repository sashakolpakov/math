import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramRawCall

namespace OAI.Algorithms

/-! Fixed outer scanner for a table of raw tuple payloads. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls



def state (rf : Fin 11 → Bool) (width modulus master shape source pay out : List Bool) : Data :=
  data rf [] width modulus master shape [] source pay out []

def ports : RecordPrograms.Ports 11 49 :=
  ⟨8,9,10,46,47,by decide,by decide,by decide,by decide⟩

def appendScopes (t d : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (rows : Rows clauses.length) (out : List Bool) : List Bool :=
  rows.foldl (fun o terms => SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBytes (clauses := clauses) t d codes terms) o) out

def loopCost (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ) : Rows clauses.length → ℕ
  | [] => 0
  | row::rows => 6*(rowBits b row).length+callbackCost t d b modulus clauses codes row+7+
      loopCost t d b modulus clauses codes rows

theorem parser_state (rf : Fin 11 → Bool) (v p f : Bool)
    (width modulus master shape src pay out : List Bool) :
    RecordPrograms.state ports (state rf width modulus master shape [] [] out) v p f src pay =
      state (RecordPrograms.state ports (state rf width modulus master shape [] [] out) v p f src pay).regs
        width modulus master shape src pay out := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecordPrograms.state,ports,state,data]

theorem parser_state_self (rf : Fin 11 → Bool) (width modulus master shape src out : List Bool)
    (h8 : rf 8=false) (h9 : rf 9=true) (h10 : rf 10=false) :
    RecordPrograms.state ports (state rf width modulus master shape [] [] out) false true false src [] =
      state rf width modulus master shape src [] out := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i
    change (Function.update (Function.update (Function.update rf 8 false) 9 true) 10 false) i=rf i
    fin_cases i <;> simp [h8,h9,h10]
  · funext i; fin_cases i <;> rfl

theorem loop_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : Rows clauses.length) (hbound : 3*clauses.length ≤ 2^b)
    (rf : Fin 11 → Bool) (width modulus shape out : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ n ≤ 1+loopCost t d b modulus clauses codes rows, ∃ rf',
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports (state rf width modulus (Encoding.encodeList id clauses) shape [] [] out)
          (rows.map (rowBits b)) [])
        (RecordPrograms.state ports
          (state rf' width modulus (Encoding.encodeList id clauses) shape [] [] (appendScopes (clauses := clauses) t d codes rows out))
          false true false [] []) := by
  induction rows generalizing rf out with
  | nil =>
      refine ⟨1,by simp [loopCost],rf,?_⟩
      apply Eval.while_false
      simp [RecordPrograms.afterTag,RecordPrograms.state,ports]
  | cons row rows ih =>
      let base := state rf width modulus (Encoding.encodeList id clauses) shape [] [] out
      let tail := Encoding.encodeList id (rows.map (rowBits b))
      let initial := RecordPrograms.state ports base false true false tail (rowBits b row).reverse
      have hin : initial=state initial.regs width modulus (Encoding.encodeList id clauses) shape tail (rowBits b row).reverse out :=
        parser_state rf false true false width modulus (Encoding.encodeList id clauses) shape tail (rowBits b row).reverse out
      obtain ⟨nc,hnc,rc,h8,h9,h10,hec⟩ := callback_eval t d ht b hb clauses codes hc row hbound
        initial.regs width modulus shape tail out hw hm hshape
      let middle := state rc width modulus (Encoding.encodeList id clauses) shape [] []
        (SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBytes (clauses := clauses) t d codes row) out)
      have hcallback : Eval callback nc initial (RecordPrograms.state ports middle false true false tail []) := by
        rw [hin,parser_state_self rc width modulus (Encoding.encodeList id clauses) shape tail _ h8 h9 h10]
        exact hec
      have hreader : Eval (RecordPrograms.reader ports) (6*(rowBits b row).length+4)
          (RecordPrograms.afterTag ports base ((row::rows).map (rowBits b)) []) initial := by
        simpa [RecordPrograms.afterTag,base,initial,tail] using
          RecordPrograms.reader_eval ports base (rowBits b row) tail [] true true false
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports middle false true false tail [])
          (RecordPrograms.afterTag ports middle (rows.map (rowBits b)) []) := by
        apply Eval.ite_false (by simp)
        simpa [tail] using RecordPrograms.pop_list_eval ports middle (rows.map (rowBits b)) [] false true
      obtain ⟨nr,hnr,rr,her⟩ := ih rc (SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBytes (clauses := clauses) t d codes row) out)
      have hguard : (RecordPrograms.afterTag ports base ((row::rows).map (rowBits b)) []).regs ports.tag=true := by
        simp [RecordPrograms.afterTag]
      refine ⟨(6*(rowBits b row).length+4+(nc+2))+nr+1,?_,rr,?_⟩
      · simp only [loopCost]; omega
      · simpa [RecordPrograms.loop,RecordPrograms.body,appendScopes,middle] using
          Eval.while_true hguard (hreader.seq (hcallback.seq hbranch)) her

abbrev iterate : Cmd 11 49 := RecordPrograms.iterate ports callback

theorem iterate_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : Rows clauses.length) (hbound : 3*clauses.length ≤ 2^b)
    (rf : Fin 11 → Bool) (width modulus shape out : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ n ≤ 3+loopCost t d b modulus clauses codes rows, ∃ rf',
      Eval iterate n
        (RecordPrograms.state ports (state rf width modulus (Encoding.encodeList id clauses) shape [] [] out)
          false false false (Encoding.encodeList id (rows.map (rowBits b))) [])
        (RecordPrograms.state ports
          (state rf' width modulus (Encoding.encodeList id clauses) shape [] [] (appendScopes (clauses := clauses) t d codes rows out))
          false true false [] []) := by
  let base := state rf width modulus (Encoding.encodeList id clauses) shape [] [] out
  have hs := RecordPrograms.set_found_eval ports base false false false false
    (Encoding.encodeList id (rows.map (rowBits b))) []
  have hp := RecordPrograms.pop_list_eval ports base (rows.map (rowBits b)) [] false false
  simp only [List.append_nil] at hp
  obtain ⟨n,hn,rf',he⟩ := loop_eval t d ht b hb clauses codes hc rows hbound rf width modulus shape out hw hm hshape
  refine ⟨1+(1+n),by omega,rf',?_⟩
  simpa [iterate,RecordPrograms.iterate,base] using hs.seq (hp.seq he)

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
