import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramCall

namespace OAI.Algorithms

/-! Fixed outer record loop: one concrete scope computation per raw hash row.
The induction is a trace proof; the instruction table contains only one loop. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Outer
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Rows := List (List Term)

def rowBits (terms : List Term) : List Bool := Encoding.encodeList payload terms
def scopeBytes (terms : List Term) : List Bool := Encoding.encodeList Encoding.encodeNat (scope terms)
def appendScopes (rows : Rows) (out : List Bool) : List Bool :=
  rows.foldl (fun o terms => SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBytes terms) o) out

def ports : RecordPrograms.Ports 11 25 :=
  ⟨8,9,10,22,23,by decide,by decide,by decide,by decide⟩

def loopCost : Rows → ℕ
  | [] => 0
  | row :: rows => 6*(rowBits row).length + callbackCost row + 7 + loopCost rows

theorem state_data (rf : Fin 11 → Bool) (v p f : Bool) (src pay out : List Bool) :
    RecordPrograms.state ports (data rf [] [] [] [] out) v p f src pay =
      data (RecordPrograms.state ports (data rf [] [] [] [] out) v p f src pay).regs [] [] src pay out := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecordPrograms.state,ports,data]

theorem state_data_self (rf : Fin 11 → Bool) (src out : List Bool)
    (h8 : rf 8=false) (h9 : rf 9=true) (h10 : rf 10=false) :
    RecordPrograms.state ports (data rf [] [] [] [] out) false true false src [] =
      data rf [] [] src [] out := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i
    by_cases h8i : i=8 <;> by_cases h9i : i=9 <;> by_cases h10i : i=10 <;>
      simp_all [RecordPrograms.state,ports,data]
  · funext i; fin_cases i <;> simp [RecordPrograms.state,ports,data]

theorem loop_eval (rows : Rows) (rf : Fin 11 → Bool) (out : List Bool) :
    ∃ t ≤ 1+loopCost rows, ∃ rf',
      Eval (RecordPrograms.loop ports callback) t
        (RecordPrograms.afterTag ports (data rf [] [] [] [] out) (rows.map rowBits) [])
        (RecordPrograms.state ports (data rf' [] [] [] [] (appendScopes rows out)) false true false [] []) := by
  induction rows generalizing rf out with
  | nil =>
      refine ⟨1,by simp [loopCost],rf,?_⟩
      apply Eval.while_false
      simp [RecordPrograms.afterTag,RecordPrograms.state,ports]
  | cons row rows ih =>
      let base := data rf [] [] [] [] out
      let tail := Encoding.encodeList id (rows.map rowBits)
      let initial := RecordPrograms.state ports base false true false tail (rowBits row).reverse
      have hin : initial = data initial.regs [] [] tail (rowBits row).reverse out :=
        state_data rf false true false tail (rowBits row).reverse out
      obtain ⟨tc,hc,rm,h8,h9,h10,he⟩ := callback_eval row initial.regs tail out
      let middle := data rm [] [] [] [] (SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBytes row) out)
      have hcallback : Eval callback tc initial
          (RecordPrograms.state ports middle false true false tail []) := by
        rw [hin,state_data_self rm tail _ h8 h9 h10]
        exact he
      have hreader : Eval (RecordPrograms.reader ports) (6*(rowBits row).length+4)
          (RecordPrograms.afterTag ports base ((row::rows).map rowBits) []) initial := by
        simpa [RecordPrograms.afterTag,base,initial,tail] using
          RecordPrograms.reader_eval ports base (rowBits row) tail [] true true false
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports middle false true false tail [])
          (RecordPrograms.afterTag ports middle (rows.map rowBits) []) := by
        apply Eval.ite_false (by simp)
        simpa [tail] using RecordPrograms.pop_list_eval ports middle (rows.map rowBits) [] false true
      obtain ⟨tr,hr,rfinal,hrest⟩ := ih rm (SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBytes row) out)
      have hguard : (RecordPrograms.afterTag ports base ((row::rows).map rowBits) []).regs ports.tag=true := by
        simp [RecordPrograms.afterTag]
      refine ⟨(6*(rowBits row).length+4+(tc+2))+tr+1,?_,rfinal,?_⟩
      · simp only [loopCost]; omega
      · simpa [RecordPrograms.loop,RecordPrograms.body,appendScopes,middle] using
          Eval.while_true hguard (hreader.seq (hcallback.seq hbranch)) hrest

abbrev iterate : Cmd 11 25 := RecordPrograms.iterate ports callback

theorem iterate_eval (rows : Rows) (rf : Fin 11 → Bool) (out : List Bool) :
    ∃ t ≤ 3+loopCost rows, ∃ rf',
      Eval iterate t
        (RecordPrograms.state ports (data rf [] [] [] [] out) false false false
          (Encoding.encodeList id (rows.map rowBits)) [])
        (RecordPrograms.state ports (data rf' [] [] [] [] (appendScopes rows out)) false true false [] []) := by
  let base := data rf [] [] [] [] out
  have hs := RecordPrograms.set_found_eval ports base false false false false
    (Encoding.encodeList id (rows.map rowBits)) []
  have hp := RecordPrograms.pop_list_eval ports base (rows.map rowBits) [] false false
  simp only [List.append_nil] at hp
  obtain ⟨t,ht,rf',he⟩ := loop_eval rows rf out
  refine ⟨1+(1+t),by omega,rf',?_⟩
  simpa [iterate,RecordPrograms.iterate,base] using hs.seq (hp.seq he)

end SubexponentialSAT.SqrtLog.HashScopeProgram.Outer

end OAI.Algorithms
