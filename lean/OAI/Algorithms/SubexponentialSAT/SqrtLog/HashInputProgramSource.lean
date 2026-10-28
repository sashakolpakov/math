import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFRecords
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Physical positional lookup in the ORIGINAL encoded clause list. The index
is a canonical natural field; all preceding records are scanned and discarded.
The master source is copied, preserved, and charged. No pre-expanded hash input
table is assumed. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Source
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

abbrev Data := State 3 6
def data (v p f : Bool) (master scan index payload tmp out : List Bool) : Data :=
  ⟨ExecCNFRecords.regs v p f, ![master,scan,index,payload,tmp,out]⟩

abbrev skip : Cmd 3 6 := .call
  (ProgramLinking.liftProgram ExecCNFRecords.skipProgram id (fun _ => (1 : Fin 6)))

theorem skip_eval (v p f : Bool) (master bits rest index payload tmp out : List Bool) :
    Eval skip (5*bits.length+8)
      (data v p f master (true :: (Encoding.frame bits ++ rest)) index payload tmp out)
      (data false true true master rest index payload tmp out) := by
  have hs : Function.Injective (fun _ : Fin 1 => (1 : Fin 6)) := by
    intro i j _; exact Subsingleton.elim i j
  let d := data v p f master (true :: (Encoding.frame bits ++ rest)) index payload tmp out
  let a : State 3 1 := ⟨ExecCNFRecords.regs v p f,
    fun _ => true :: (Encoding.frame bits ++ rest)⟩
  let b : State 3 1 := ⟨ExecCNFRecords.regs false true true, fun _ => rest⟩
  have hi : embedState id (fun _ : Fin 1 => (1 : Fin 6)) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id hs
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i; rfl
    · intros; rfl
  have ho : embedState id (fun _ : Fin 1 => (1 : Fin 6)) d b =
      data false true true master rest index payload tmp out := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id hs
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i; rfl
    · intro i hi
      have hn : i ≠ 1 := fun h => hi ⟨0,h.symm⟩
      fin_cases i <;> simp_all [d,data]
  have h := eval_call_lifted ExecCNFRecords.skipProgram id (fun _ => (1 : Fin 6))
    d Function.injective_id hs (a := a) (b := b)
    (ExecCNFRecords.record_trace bits rest v p f)
  rw [hi,ho] at h
  exact h

abbrev popIndex : Cmd 3 6 := .base (.atom (.pop 2 0 1))

theorem popIndex_eval (v p f b : Bool) (master scan index payload tmp out : List Bool) :
    Eval popIndex 1 (data v p f master scan (b::index) payload tmp out)
      (data b true f master scan index payload tmp out) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (2 : Fin 6) (0 : Fin 3) 1)
    (data v p f master scan (b::index) payload tmp out))) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [data,ExecCNFRecords.regs,
      StructuredProgram.Atom.instr,
      execInstr,readRegs]
  · funext i; fin_cases i <;> simp [data,
      StructuredProgram.Atom.instr,
      execInstr]

abbrev skipLoop : Cmd 3 6 := .while 0 (.seq skip popIndex)

def recordPrefix (xs : List (List Bool)) : List Bool :=
  xs.foldr (fun bits tail => true :: (Encoding.frame bits ++ tail)) []

def skipCost (xs : List (List Bool)) : ℕ :=
  (xs.map (fun bits => 5*bits.length+10)).sum

theorem skipLoop_eval (xs : List (List Bool)) (master rest payload tmp out : List Bool)
    (f : Bool) :
    Eval skipLoop (skipCost xs+1)
      (data (!xs.isEmpty) true f master (recordPrefix xs ++ rest)
        ((Encoding.encodeNat xs.length).tail) payload tmp out)
      (data false true (if xs=[] then f else true) master rest [] payload tmp out) := by
  induction xs generalizing f with
  | nil => simpa [skipLoop,skipCost,recordPrefix,Encoding.encodeNat,data] using
      (Eval.while_false (test := (0 : Fin 3))
        (body := .seq skip popIndex) (a := data false true f master rest [] payload tmp out) rfl)
  | cons x xs ih =>
      have hskip := skip_eval true true f master x (recordPrefix xs ++ rest)
        (Encoding.encodeNat xs.length) payload tmp out
      have hp := popIndex_eval false true true (!xs.isEmpty) master (recordPrefix xs ++ rest)
        ((Encoding.encodeNat xs.length).tail) payload tmp out
      have hc : Encoding.encodeNat xs.length =
          (!xs.isEmpty) :: (Encoding.encodeNat xs.length).tail := by
        cases xs <;> simp [Encoding.encodeNat,List.replicate_succ]
      rw [← hc] at hp
      have hi := ih true
      have hh := Eval.while_true (test := (0 : Fin 3)) rfl (hskip.seq hp) hi
      convert hh using 1 <;>
        simp [skipCost,recordPrefix,Encoding.encodeNat,List.replicate_succ,
          List.append_assoc] ; omega

abbrev skipPrefix : Cmd 3 6 := .seq popIndex skipLoop

theorem skipPrefix_eval (xs : List (List Bool)) (v p f : Bool)
    (master rest payload tmp out : List Bool) :
    Eval skipPrefix (skipCost xs+2)
      (data v p f master (recordPrefix xs ++ rest) (Encoding.encodeNat xs.length) payload tmp out)
      (data false true (if xs=[] then f else true) master rest [] payload tmp out) := by
  have hp := popIndex_eval v p f (!xs.isEmpty) master (recordPrefix xs ++ rest)
    ((Encoding.encodeNat xs.length).tail) payload tmp out
  have hc : Encoding.encodeNat xs.length =
      (!xs.isEmpty) :: (Encoding.encodeNat xs.length).tail := by
    cases xs <;> simp [Encoding.encodeNat,List.replicate_succ]
  rw [← hc] at hp
  have hh := hp.seq (skipLoop_eval xs master rest payload tmp out f)
  simpa only [skipPrefix,show 1+(skipCost xs+1)=skipCost xs+2 by omega] using hh

def ports : RecordPrograms.Ports 3 6 where
  tag := 0; present := 1; found := 2; source := 1; payload := 3
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

theorem parser_state (v p f v' p' f' : Bool)
    (master scan index payload tmp out scan' payload' : List Bool) :
    RecordPrograms.state ports (data v p f master scan index payload tmp out)
      v' p' f' scan' payload' = data v' p' f' master scan' index payload' tmp out := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

abbrev popTag : Cmd 3 6 := .base (.atom (.pop 1 0 1))

theorem popTag_eval (v p f b : Bool) (master scan index payload tmp out : List Bool) :
    Eval popTag 1 (data v p f master (b::scan) index payload tmp out)
      (data b true f master scan index payload tmp out) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (1 : Fin 6) (0 : Fin 3) 1)
    (data v p f master (b::scan) index payload tmp out))) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [data,ExecCNFRecords.regs,
      StructuredProgram.Atom.instr,
      execInstr,readRegs]
  · funext i; fin_cases i <;> simp [data,
      StructuredProgram.Atom.instr,
      execInstr]

abbrev readSelected : Cmd 3 6 := .seq popTag (RecordPrograms.reader ports)

theorem readSelected_eval (v p f : Bool) (master bits rest out : List Bool) :
    Eval readSelected (6*bits.length+5)
      (data v p f master (true :: (Encoding.frame bits ++ rest)) [] [] [] out)
      (data false true f master rest [] bits.reverse [] out) := by
  have hp := popTag_eval v p f true master (Encoding.frame bits ++ rest) [] [] [] out
  have hr := RecordPrograms.reader_eval ports
    (data true true f master (Encoding.frame bits ++ rest) [] [] [] out)
    bits rest [] true true f
  simp only [parser_state,List.append_nil] at hr
  simpa only [readSelected,show 1+(6*bits.length+4)=6*bits.length+5 by omega] using hp.seq hr

end SubexponentialSAT.SqrtLog.HashInputProgram.Source

end OAI.Algorithms
