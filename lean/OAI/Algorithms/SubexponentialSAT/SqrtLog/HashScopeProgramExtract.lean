import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramBytes
import OAI.Algorithms.SubexponentialSAT.ExecCNFRecords
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! Physical extraction of the literal-record bytes from one weighted raw
clause. Coefficient bytes are discarded even when the coefficient is zero. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Extract
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 3 6

def data (v p f : Bool) (source payload scan weight out tmp : List Bool) : Data :=
  ⟨ExecCNFRecords.regs v p f, ![source,payload,scan,weight,out,tmp]⟩

abbrev move12 : Cmd 3 6 := .call (StackRoutines.transferProgram 1 2 0 1)
abbrev move25 : Cmd 3 6 := .call (StackRoutines.transferProgram 2 5 0 1)
abbrev move54 : Cmd 3 6 := .call (StackRoutines.transferProgram 5 4 0 1)
abbrev clear3 : Cmd 3 6 := .call (StackRoutines.clearProgram 3 0 1)
abbrev pop5 : Cmd 3 6 := .base (.atom (.pop 5 0 1))
abbrev finish : Cmd 3 6 := .base (.atom (.set 1 true))

theorem move12_eval (v p f : Bool) (s x w o t : List Bool) :
    Eval move12 (3*x.length+3) (data v p f s x [] w o t)
      (data false false f s [] x.reverse w o t) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.transfer_eval (1 : Fin 6) 2 (0 : Fin 3) 1
    (by decide) (by decide) (data v p f s x [] w o t)
  convert h using 1
  · simp [data]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> simp [data, ExecCNFRecords.regs, readRegs]
    · funext i; fin_cases i <;> simp [data, StackRoutines.transferStacks]

theorem move25_eval (v p f : Bool) (s x w o : List Bool) :
    Eval move25 (3*x.length+3) (data v p f s [] x w o [])
      (data false false f s [] [] w o x.reverse) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.transfer_eval (2 : Fin 6) 5 (0 : Fin 3) 1
    (by decide) (by decide) (data v p f s [] x w o [])
  convert h using 1
  · simp [data]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> simp [data, ExecCNFRecords.regs, readRegs]
    · funext i; fin_cases i <;> simp [data, StackRoutines.transferStacks]

theorem move54_eval (v p f : Bool) (s o t : List Bool) :
    Eval move54 (3*t.length+3) (data v p f s [] [] [] o t)
      (data false false f s [] [] [] (t.reverse++o) []) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.transfer_eval (5 : Fin 6) 4 (0 : Fin 3) 1
    (by decide) (by decide) (data v p f s [] [] [] o t)
  convert h using 1
  · simp [data]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> simp [data, ExecCNFRecords.regs, readRegs]
    · funext i; fin_cases i <;> simp [data, StackRoutines.transferStacks]

theorem clear3_eval (v p f : Bool) (s x w o t : List Bool) :
    Eval clear3 (2*w.length+3) (data v p f s [] x w o t)
      (data false false f s [] x [] o t) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.clear_eval (3 : Fin 6) (0 : Fin 3) 1
    (data v p f s [] x w o t)
  convert h using 1
  · simp [data]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> simp [data, ExecCNFRecords.regs, readRegs]
    · funext i; fin_cases i <;> simp [data, StackRoutines.clearStacks]

theorem pop5_eval (v p f : Bool) (s o t : List Bool) :
    Eval pop5 1 (data v p f s [] [] [] o (false::t))
      (data false true f s [] [] [] o t) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (5 : Fin 6) (0 : Fin 3) 1)
    (data v p f s [] [] [] o (false::t)))) using 1
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [data,ExecCNFRecords.regs,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
      execInstr,readRegs]
  · funext i; fin_cases i <;> simp [data,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
      execInstr]

theorem finish_eval (s o : List Bool) :
    Eval finish 1 (data false false false s [] [] [] o [])
      (data false true false s [] [] [] o []) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.set (s := 6) (1 : Fin 3) true)
    (data false false false s [] [] [] o []))) using 1
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [data,ExecCNFRecords.regs,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
      execInstr]
  · rfl

def weightPorts : RecordPrograms.Ports 3 6 :=
  ⟨0,1,2,2,3,by decide,by decide,by decide,by decide⟩

theorem reader_eval (s w clause out : List Bool) :
    Eval (RecordPrograms.reader weightPorts) (6*w.length+4)
      (data false false false s [] (Encoding.frame w ++ clause) [] out [])
      (data false true false s [] clause w.reverse out []) := by
  have h := RecordPrograms.reader_eval weightPorts
    (data false false false s [] [] [] out []) w clause [] false false false
  convert h using 1 <;>
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext <;>
    (funext i; fin_cases i <;> simp [RecordPrograms.state,weightPorts,data,ExecCNFRecords.regs])

abbrev command : Cmd 3 6 := .seq move12 (.seq (RecordPrograms.reader weightPorts)
  (.seq clear3 (.seq move25 (.seq pop5 (.seq move54 finish)))))

theorem command_eval (w s out : List Bool) (records : List (List Bool)) :
    ∃ t ≤ 30*((Encoding.frame w ++ Encoding.encodeList id records).length+1),
      Eval command t
        (data false true false s (Encoding.frame w ++ Encoding.encodeList id records).reverse [] [] out [])
        (data false true false s [] [] [] (recordPrefix records ++ out) []) := by
  let clause := Encoding.encodeList id records
  let bits := Encoding.frame w ++ clause
  have h1 := move12_eval false true false s bits.reverse [] out []
  simp only [List.length_reverse,List.reverse_reverse] at h1
  have h2 := reader_eval s w clause out
  have h3 := clear3_eval false true false s clause w.reverse out []
  simp only [List.length_reverse] at h3
  have h4 := move25_eval false false false s clause [] out
  have hr : clause.reverse = false :: (recordPrefix records).reverse := by
    simp [clause,encodeRecords_eq]
  rw [hr] at h4
  have h5 := pop5_eval false false false s out (recordPrefix records).reverse
  have h6 := move54_eval false true false s out (recordPrefix records).reverse
  simp only [List.length_reverse,List.reverse_reverse] at h6
  have h7 := finish_eval s (recordPrefix records ++ out)
  refine ⟨_, ?_, h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))⟩
  have hc : (Encoding.encodeList id records).length = (recordPrefix records).length+1 := by
    simp [encodeRecords_eq]
  dsimp [bits,clause]
  simp only [List.length_append,Encoding.length_frame]
  omega

end SubexponentialSAT.SqrtLog.HashScopeProgram.Extract

end OAI.Algorithms
