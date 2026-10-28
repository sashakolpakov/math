import OAI.Algorithms.SubexponentialSAT.BitProgramSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgramBridge
import Mathlib.Data.List.Forall2

/-! Immediate Boolean specialization using the actual dictionary scanner. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset
open OAI BitProgram StructuredProgram

def below : List Bool → List Bool → Bool
  | [], _ => true
  | b::bs, qs => (!b || qs.headD false) && below bs qs.tail

def data (r : Fin 5 → Bool) (mask query saved : List Bool) : State 5 3 :=
  ⟨r,![mask,query,saved]⟩

def ready (r : Fin 5 → Bool) (mask query saved : List Bool) : State 5 3 :=
  data (readRegs r 0 1 mask.head?) mask query saved

def body : Cmd 5 3 :=
  .seq (.atom (.pop 0 0 1)) <|
  .seq (.atom (.pop 1 2 3)) <|
  .seq (.atom (.push 2 2)) <|
  .seq (.atom (.bnot 0 0)) <|
  .seq (.atom (.bor 0 0 2)) <|
  .seq (.atom (.band 4 4 0)) (.atom (.peek 0 0 1))

def loop : Cmd 5 3 := .while 1 body

def command : Cmd 5 3 := .seq (.atom (.set 4 true))
  (.seq (.atom (.peek 0 0 1)) loop)

theorem body_eval (r : Fin 5 → Bool) (b q : Bool) (bs qs saved : List Bool) :
    ∃ rf, Eval body 7 (data r (b::bs) (q::qs) saved)
      (ready rf bs qs (q::saved)) ∧ rf 4 = (r 4 && (!b || q)) := by
  let d0 := data r (b::bs) (q::qs) saved
  let d1 := (Atom.pop (0:Fin 3) (0:Fin 5) 1).eval d0
  let d2 := (Atom.pop (1:Fin 3) (2:Fin 5) 3).eval d1
  let d3 := (Atom.push (2:Fin 3) (2:Fin 5)).eval d2
  let d4 := (Atom.bnot (0:Fin 5) 0).eval d3
  let d5 := (Atom.bor (0:Fin 5) 0 2).eval d4
  let d6 := (Atom.band (4:Fin 5) 4 0).eval d5
  have h := (Eval.atom (Atom.pop (0:Fin 3) (0:Fin 5) 1) d0).seq
    ((Eval.atom (Atom.pop (1:Fin 3) (2:Fin 5) 3) d1).seq
    ((Eval.atom (Atom.push (2:Fin 3) (2:Fin 5)) d2).seq
    ((Eval.atom (Atom.bnot (0:Fin 5) 0) d3).seq
    ((Eval.atom (Atom.bor (0:Fin 5) 0 2) d4).seq
    ((Eval.atom (Atom.band (4:Fin 5) 4 0) d5).seq
    (Eval.atom (Atom.peek (0:Fin 3) (0:Fin 5) 1) d6))))))
  refine ⟨d6.regs,?_,?_⟩
  · convert h using 1
    · rfl
    · apply congrArg₂ State.mk
      · rfl
      · funext i; fin_cases i <;> simp [d0,d1,d2,d3,d4,d5,d6,data,
          Atom.eval,Atom.instr,State.ofCfg,execInstr,readRegs]
  · simp [d0,d1,d2,d3,d4,d5,d6,data,Atom.eval,Atom.instr,
      State.ofCfg,execInstr,readRegs]

theorem loop_eval (mask query saved : List Bool) (r : Fin 5 → Bool)
    (hl : mask.length = query.length) :
    ∃ rf, Eval loop (8*mask.length+1) (ready r mask query saved)
      (data rf [] [] (query.reverse++saved)) ∧ rf 4 = (r 4 && below mask query) := by
  induction mask generalizing query saved r with
  | nil =>
    have hq : query=[] := List.length_eq_zero_iff.mp hl.symm
    subst query
    refine ⟨(ready r [] [] saved).regs,?_,?_⟩
    · simpa [loop,ready,data] using
        (Eval.while_false (body:=body) (by simp [ready,data,readRegs] :
          (ready r [] [] saved).regs 1 = false))
    · simp [ready,data,readRegs,below]
  | cons b bs ih =>
    cases query with
    | nil => simp at hl
    | cons q qs =>
      obtain ⟨rb,hb,hv⟩ := body_eval (readRegs r 0 1 (some b)) b q bs qs saved
      obtain ⟨rf,hf,hout⟩ := ih qs (q::saved) rb (by simpa using hl)
      refine ⟨rf,?_,?_⟩
      · have hh := Eval.while_true (body:=body)
          (by simp [ready,data,readRegs] : (ready r (b::bs) (q::qs) saved).regs 1=true) hb hf
        convert hh using 1 <;> simp [loop,data,List.reverse_cons,List.append_assoc]
        omega
      · rw [hout,hv]
        simp [readRegs,below,Bool.and_assoc]

theorem command_eval (mask query : List Bool) (r : Fin 5 → Bool)
    (hl : mask.length = query.length) :
    ∃ rf, Eval command (8*mask.length+3) (data r mask query [])
      (data rf [] [] query.reverse) ∧ rf 4 = below mask query := by
  let r1 := Function.update r 4 true
  have hs : Eval (.atom (.set 4 true)) 1 (data r mask query [])
      (data r1 mask query []) := Eval.atom _ _
  have hp : Eval (.atom (.peek 0 0 1)) 1 (data r1 mask query [])
      (ready r1 mask query []) := Eval.atom _ _
  obtain ⟨rf,hf,hv⟩ := loop_eval mask query [] r1 hl
  refine ⟨rf,?_,by simpa [r1] using hv⟩
  convert hs.seq (hp.seq hf) using 1
  · rfl
  · omega
  · simp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset
open OAI BitProgram StructuredProgram

theorem below_eq_true (mask query : List Bool) (hl : mask.length=query.length) :
    below mask query = true ↔ List.Forall₂ (fun b q => b=true → q=true) mask query := by
  induction mask generalizing query with
  | nil =>
    have hq : query=[] := List.length_eq_zero_iff.mp hl.symm
    subst query
    simp [below]
  | cons b bs ih =>
    cases query with
    | nil => simp at hl
    | cons q qs =>
      rw [below,List.forall₂_cons]
      simp only [List.headD_cons,List.tail_cons]
      rw [Bool.and_eq_true,ih qs (by simpa using hl)]
      cases b <;> cases q <;> simp

theorem below_reverse (mask query : List Bool) (hl : mask.length=query.length) :
    below mask.reverse query.reverse = below mask query := by
  apply Bool.eq_iff_iff.mpr
  rw [below_eq_true _ _ (by simpa using hl),below_eq_true _ _ hl,List.forall₂_reverse_iff]

def program := compiled command 0 2

theorem program_trace (mask query : List Bool) (r : Fin 5 → Bool)
    (hl : mask.length=query.length) :
    ∃ rf, Trace program (8*mask.length+4)
      ((data r mask query []).withPC (some program.entry))
      ((data rf [] [] query.reverse).withPC none) ∧ rf 4=below mask query := by
  obtain ⟨rf,hf,hv⟩ := command_eval mask query r hl
  exact ⟨rf,by simpa [program,Nat.add_assoc] using compiled_halt_trace hf 0 2,hv⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset

/-! The dictionary framing, key rewrite and record traversal follow the actual
MomentsProjectionProgramNative implementation. The replacement comparator tests
support inclusion, so this scan implements evaluation at a Boolean correction
assignment. Numeric-key collisions are intentionally left for normalization. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog MomentsProjectionProgram

def subsetPorts : Fin 3 → Fin 10 := ![2,1,6]
theorem subsetPorts_injective : Function.Injective subsetPorts := by decide

def scanSubset : Cmd 5 10 := .call
  (ProgramLinking.liftProgram Subset.program id subsetPorts)
def compare : Cmd 5 10 := .seq scanSubset (transfer 6 1)

theorem compare_eval (regs : Fin 5 → Bool) (a : Tape) (key query : List Bool)
    (hk : a.key=key.reverse) (hq : a.target=query.reverse) (ht : a.tmp=[])
    (hl : key.length=query.length) :
    ∃ time ≤ 11*key.length+9*query.length+21, ∃ rf,
      Eval compare time (machine regs a) (machine rf {a with key:=[],tmp:=[]}) ∧
      rf 4 = Subset.below key query := by
  obtain ⟨rr,hh,hv⟩ := Subset.program_trace key.reverse query.reverse regs (by simpa using hl)
  let b := Subset.data rr [] [] query
  have ha : embedState id subsetPorts (machine regs a)
      (Subset.data regs key.reverse query.reverse []) = machine regs a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id subsetPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [Subset.data,subsetPorts,machine,tapes,hk,hq,ht]
    · intros; rfl
  have hb : embedState id subsetPorts (machine regs a) b =
      machine rr {a with key:=[],target:=[],tmp:=query} := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id subsetPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> simp_all [subsetPorts,machine,tapes,Fin.exists_fin_succ]
  have hs := eval_call_lifted Subset.program id subsetPorts (machine regs a)
    Function.injective_id subsetPorts_injective hh
  have hs' : Eval scanSubset (8*key.length+4) (machine regs a)
      (machine rr {a with key:=[],target:=[],tmp:=query}) := by
    simpa only [ha,List.reverse_reverse,List.length_reverse,hb,scanSubset,b] using hs
  have ht' := transfer_machine rr {a with key:=[],target:=[],tmp:=query}
    {a with key:=[],tmp:=[]} 6 1 (by decide) (by
      funext i; fin_cases i <;> simp [StackRoutines.transferStacks,tapes,hq])
  refine ⟨(8*key.length+4)+(3*query.length+3),by omega,readRegs rr 0 1 none,?_,?_⟩
  · simpa [compare,tapes] using hs'.seq ht'
  · simpa [readRegs,Subset.below_reverse _ _ hl] using hv

def record : Cmd 5 10 := .seq (readFrame 0 2) (.seq (readFrame 0 3)
  (.seq rewriteKey (.seq compare (.ite 4 hit miss))))
def recordBody : Cmd 5 10 := .seq record (.base (.atom (.peek 0 0 3)))
def records : Cmd 5 10 := .while 3 recordBody

def selected (query : List Bool) : List Entry → List Entry
  | [] => []
  | e::es => if Subset.below e.mask query = true then e.erased::selected query es
      else selected query es

def project : Cmd 5 10 := .seq (readFrame 0 1)
  (.seq (.base (.atom (.peek 0 0 3))) (.seq records (transfer 8 9)))
def program := compiled project 0 9

theorem record_eval (regs : Fin 5 → Bool) (u z : ℕ)
    (mask coeff rest query output : List Bool) (hl : mask.length=query.length) :
    ∃ time ≤ 100*((recordBits u z mask coeff).length+query.length+1), ∃ rf,
      Eval record time
        (machine regs (clean (recordBits u z mask coeff++rest) query output))
        (machine rf (clean rest query
          (if Subset.below mask query = true then (recordBits u z (List.replicate mask.length false) coeff).reverse++output
           else output))) := by
  let r₁ := readRegs regs (0:Fin 5) 1 (some false)
  let r₂ := readRegs r₁ (0:Fin 5) 1 (some false)
  have h₁ := read_key regs u z mask coeff rest query output
  have h₂ := read_coeff r₁ (keyBits u z mask).reverse coeff rest query output
  let a : Tape := {clean rest query output with key:=(keyBits u z mask).reverse,coeff:=coeff.reverse}
  obtain ⟨r₃,h₃⟩ := rewriteKey_eval r₂ a u z mask rfl rfl rfl
  let b : Tape := {clean rest query output with key:=mask.reverse,coeff:=coeff.reverse, newkey:=(keyBits u z (List.replicate mask.length false)).reverse}
  have h₃' : Eval rewriteKey
      (3*(keyBits u z mask).length+4*u+4*z+6*mask.length+16)
      (machine r₂ a) (machine r₃ b) := by
    simpa [a,b,keyBits,clean] using h₃
  obtain ⟨tc,htc,r₄,h₄,hr₄⟩ := compare_eval r₃ b mask query rfl rfl rfl hl
  let c : Tape := {clean rest query output with coeff:=coeff.reverse, newkey:=(keyBits u z (List.replicate mask.length false)).reverse}
  have h₄' : Eval compare tc (machine r₃ b) (machine r₄ c) := by
    simpa [b,c,clean] using h₄
  by_cases heq : Subset.below mask query = true
  · obtain ⟨rf,h₅⟩ := hit_eval r₄ c (keyBits u z (List.replicate mask.length false)) coeff rfl rfl rfl
    have h₅' := Eval.ite_true (yes:=hit) (no:=miss)
      (by simp [machine,hr₄,heq] : (machine r₄ c).regs 4=true) h₅
    have hall := h₁.seq (h₂.seq (h₃'.seq (h₄'.seq h₅')))
    refine ⟨_,?_,rf,by simpa [record,a,c,clean,heq,recordBits,keyBits] using hall⟩
    simp [recordBits_length]
    omega
  · obtain ⟨rf,h₅⟩ := miss_eval r₄ c
    have h₅' := Eval.ite_false (yes:=hit) (no:=miss)
      (by simp [machine,hr₄,heq] : (machine r₄ c).regs 4=false) h₅
    have hall := h₁.seq (h₂.seq (h₃'.seq (h₄'.seq h₅')))
    refine ⟨_,?_,rf,by simpa [record,a,c,clean,heq] using hall⟩
    simp [recordBits_length]
    omega


theorem records_eval (es : List Entry) (regs : Fin 5 → Bool) (query output : List Bool)
    (hlen : ∀ e ∈ es, e.mask.length=query.length) :
    ∃ time ≤ loopBudget query es, ∃ rf, Eval records time
      (readyRecords regs (raw es) query output)
      (machine rf (clean [] query ((raw (selected query es)).reverse++output))) := by
  induction es generalizing regs output with
  | nil =>
      refine ⟨1,le_rfl,(readyRecords regs [] query output).regs,?_⟩
      simpa [records,raw,selected,readyRecords,machine,clean] using
        (Eval.while_false (body:=recordBody) (readyRecords_guard regs [] query output))
  | cons e es ih =>
      obtain ⟨tr,htr,rr,hr⟩ := record_eval (readyRecords regs (raw (e::es)) query output).regs
        e.u e.z e.mask e.coeff (raw es) query output (hlen e (by simp))
      let out := if Subset.below e.mask query = true then e.erased.bits.reverse++output else output
      have hr' : Eval record tr (readyRecords regs (raw (e::es)) query output)
          (machine rr (clean (raw es) query out)) := by
        simpa [raw,readyRecords,out,Entry.erased,Entry.bits,machine,clean] using hr
      have hp : Eval (.base (.atom (.peek 0 0 3))) 1
          (machine rr (clean (raw es) query out)) (readyRecords rr (raw es) query out) :=
        Eval.base (StructuredProgram.Eval.atom _ _)
      obtain ⟨tt,htt,rf,ht⟩ := ih rr out (by intro f hf; exact hlen f (List.mem_cons_of_mem e hf))
      have hall := Eval.while_true (body:=recordBody)
        (readyRecords_cons_guard regs e es query output) (hr'.seq hp) ht
      refine ⟨tr+1+tt+1,?_,rf,?_⟩
      · dsimp [loopBudget]; change tr ≤ _ at htr
        simpa [Entry.bits] using (show tr+1+tt+1 ≤
          100*((recordBits e.u e.z e.mask e.coeff).length+query.length+1)+2+loopBudget query es by omega)
      · by_cases h : Subset.below e.mask query = true <;>
          simpa [records,selected,h,raw,out,Entry.bits,Entry.erased,
            List.reverse_append,List.append_assoc] using hall


theorem selected_length (query : List Bool) (es : List Entry) :
    (raw (selected query es)).length ≤ (raw es).length := by
  induction es with
  | nil => simp [selected,raw]
  | cons e es ih =>
      by_cases h : Subset.below e.mask query = true
      · simp [selected,h,raw,Entry.erased,Entry.bits,recordBits_length] at *;omega
      · simp [selected,h,raw];omega


theorem project_eval (regs : Fin 5 → Bool) (query : List Bool) (es : List Entry) (hlen : ∀ e ∈ es, e.mask.length=query.length) :
    ∃ time ≤ 200*((raw es).length+1)*(query.length+2), ∃ rf,
      Eval project time (machine regs {input:=input query es})
        (machine rf {target:=query.reverse,framed:=raw (selected query es)}) := by
  let a : Tape := {input:=input query es}
  let r₁ := readRegs regs (0:Fin 5) 1 (some false)
  have h₁ := readFrame_eval (machine regs a) 0 1 (by decide) query (raw es) rfl
  have h₁' : Eval (readFrame 0 1) (6*query.length+4) (machine regs a)
      (machine r₁ (clean (raw es) query [])) := by
    convert h₁ using 1
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [machine,tapes,a,clean]
  have hp : Eval (.base (.atom (.peek 0 0 3))) 1
      (machine r₁ (clean (raw es) query [])) (readyRecords r₁ (raw es) query []) :=
    Eval.base (StructuredProgram.Eval.atom _ _)
  obtain ⟨tt,htt,rr,ht⟩ := records_eval es r₁ query [] hlen
  let b : Tape := clean [] query (raw (selected query es)).reverse
  have ht' : Eval records tt (readyRecords r₁ (raw es) query []) (machine rr b) := by
    simpa [b] using ht
  let c : Tape := {target:=query.reverse,framed:=raw (selected query es)}
  have hf := transfer_machine rr b c 8 9 (by decide) (by
    funext i; fin_cases i <;> simp [StackRoutines.transferStacks,tapes,b,c,clean])
  have hall := h₁'.seq (hp.seq (ht'.seq hf))
  refine ⟨_,?_,readRegs rr 0 1 none,by simpa [project,a,b,c,tapes,clean] using hall⟩
  have hbudget := loopBudget_bound query es
  have hcount := raw_count es
  have hlen := selected_length query es
  have hprod := Nat.mul_le_mul_left (query.length+1) hcount
  nlinarith

/-- Primitive instruction trace with explicit serialized input and output. -/
theorem serializedEval (regs : Fin 5 → Bool) (query : List Bool) (es : List Entry) (hlen : ∀ e ∈ es, e.mask.length=query.length) :
    ∃ rf, RunsIn program (200*((raw es).length+1)*(query.length+2)+1)
      ((machine regs {input:=input query es}).withPC (some program.entry))
      ((machine rf {target:=query.reverse,framed:=raw (selected query es)}).withPC none) := by
  obtain ⟨time,htime,rf,h⟩ := project_eval regs query es hlen
  exact ⟨rf,time+1,Nat.add_le_add_right htime 1,compiled_halt_trace h 0 9⟩


open Squarefree

theorem below_encodeMask {n : ℕ} (s U : Finset (Fin n)) :
    Subset.below (encodeMask s) (encodeMask U) = decide (s ⊆ U) := by
  apply Bool.eq_iff_iff.mpr
  rw [Subset.below_eq_true _ _ (by simp),decide_eq_true_eq]
  constructor
  · intro h v hv
    have hh := h.get (i:=v.val) (by simp) (by simp)
    simp [encodeMask] at hh
    exact hh hv
  · intro h
    apply List.forall₂_of_length_eq_of_get (by simp)
    intro i hi hj
    have hi' : i<n := by simpa using hi
    simpa [encodeMask] using (show (⟨i,hi'⟩:Fin n) ∈ s → (⟨i,hi'⟩:Fin n) ∈ U from fun hv => h hv)

theorem selected_ofIndex {n : ℕ} (U : Finset (Fin n))
    (l : List (Index (Fin n) × List Bool)) :
    selected (encodeMask U) (l.map ofIndex) =
      (HeadEvaluation.specializeEntries U l).map ofIndex := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a.1.vars ⊆ U <;>
      simp [selected,ofIndex,below_encodeMask,h,HeadEvaluation.specializeEntries,
        ih,Entry.erased,encodeMask_empty]

/-- The fixed native scanner performs immediate Boolean specialization before
any dictionary multiplication. Duplicate numeric keys await normalization. -/
theorem raw_dictionary_runsIn {n : ℕ} (U : Finset (Fin n))
    (l : List (Index (Fin n) × List Bool)) (regs : Fin 5 → Bool) :
    ∃ rf, RunsIn program
      (200*((Squarefree.Program.rawEntries (l.map fun a => (encodeIndex a.1,a.2))).length+1)*(n+2)+1)
      ((machine regs {input:=Encoding.frame (encodeMask U)++
        Squarefree.Program.rawEntries (l.map fun a => (encodeIndex a.1,a.2))}).withPC (some program.entry))
      ((machine rf {target:=(encodeMask U).reverse,framed:=
        Squarefree.Program.rawEntries ((HeadEvaluation.specializeEntries U l).map
          fun a => (encodeIndex a.1,a.2))}).withPC none) := by
  have hl : ∀ e ∈ l.map ofIndex, e.mask.length=(encodeMask U).length := by
    intro e he
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp he
    simp [ofIndex]
  simpa [input,raw_ofIndex,selected_ofIndex] using
    serializedEval regs (encodeMask U) (l.map ofIndex) hl

/-- Every stack, including retained mask, parser buffers, original records and
new records, is included throughout this polynomial local routine. -/
theorem raw_dictionary_run_space {n : ℕ} (U : Finset (Fin n))
    (l : List (Index (Fin n) × List Bool)) (regs : Fin 5 → Bool) :
    let source := Squarefree.Program.rawEntries (l.map fun a => (encodeIndex a.1,a.2))
    let budget := 200*(source.length+1)*(n+2)+1
    ∃ steps ≤ budget, ∃ rf,
      Trace program steps
        ((machine regs {input:=Encoding.frame (encodeMask U)++source}).withPC (some program.entry))
        ((machine rf {target:=(encodeMask U).reverse,framed:=
          Squarefree.Program.rawEntries ((HeadEvaluation.specializeEntries U l).map
            fun a => (encodeIndex a.1,a.2))}).withPC none) ∧
      ∀ j ≤ steps, ∀ c, Trace program j
        ((machine regs {input:=Encoding.frame (encodeMask U)++source}).withPC (some program.entry)) c →
        dataBits c ≤ source.length+2*n+2+budget := by
  dsimp only
  obtain ⟨rf,steps,hsteps,ht⟩ := raw_dictionary_runsIn U l regs
  refine ⟨steps,hsteps,rf,ht,?_⟩
  intro j hj c hc
  have hb := trace_dataBits program hc
  have hi : dataBits ((machine regs {input:=Encoding.frame (encodeMask U)++
        Squarefree.Program.rawEntries (l.map fun a => (encodeIndex a.1,a.2))}).withPC (some program.entry)) =
      (Squarefree.Program.rawEntries (l.map fun a => (encodeIndex a.1,a.2))).length+2*n+1 := by
    simp [dataBits,stackBits,machine,tapes,Fin.sum_univ_succ,
      Nat.add_assoc,Nat.add_comm]
  rw [hi] at hb
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization
