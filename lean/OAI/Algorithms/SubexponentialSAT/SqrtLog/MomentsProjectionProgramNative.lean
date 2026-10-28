import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgramBase

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- The mask service preserves all tape fields outside work/key/newkey. -/
theorem scanMask_eval (regs : Fin 5 → Bool) (a : Tape) :
    ∃ rf, Eval scanMask (6*a.work.length+3) (machine regs a)
      (machine rf {a with work:=[],key:=a.work.reverse++a.key, newkey:=List.replicate a.work.length false++a.newkey}) := by
  obtain ⟨rr,hh⟩ := scan_trace a.work a.key a.newkey (regs ∘ smallRegs)
  let b := maskData rr [] (a.work.reverse++a.key) (List.replicate a.work.length false++a.newkey)
  let rf := (embedState smallRegs maskPorts (machine regs a) b).regs
  have ha : embedState smallRegs maskPorts (machine regs a)
      (maskData (regs ∘ smallRegs) a.work a.key a.newkey) = machine regs a := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective maskPorts_injective
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hb : embedState smallRegs maskPorts (machine regs a) b =
      machine rf {a with work:=[],key:=a.work.reverse++a.key, newkey:=List.replicate a.work.length false++a.newkey} := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective maskPorts_injective
    · intro i; exact embedState_register smallRegs maskPorts (machine regs a) b smallRegs_injective i
    · intro i hi; exact embedState_register_frame smallRegs maskPorts (machine regs a) b i hi
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> simp_all [maskPorts,machine,tapes,Fin.exists_fin_succ]
  have h := eval_call_lifted scanProgram smallRegs maskPorts (machine regs a)
    smallRegs_injective maskPorts_injective hh
  exact ⟨rf,by simpa only [ha,hb,scanMask,b] using h⟩

/-- Emit one framed record without touching the outer source or accumulated output. -/
theorem emit_eval (regs : Fin 5 → Bool) (a : Tape) (key coeff : List Bool)
    (hk : a.newkey = key.reverse) (hc : a.coeff = coeff.reverse) :
    ∃ rf, Eval emit (4*key.length+4*coeff.length+13) (machine regs a)
      (machine rf {a with newkey:=[],coeff:=[], framed:=Encoding.frame key++Encoding.frame coeff++a.framed}) := by
  obtain ⟨rr,hh⟩ := Squarefree.Program.prependRecord_trace (regs ∘ smallRegs) key coeff a.framed
  let b := Squarefree.Program.prependData rr [] []
    (Encoding.frame key++Encoding.frame coeff++a.framed)
  let rf := (embedState smallRegs emitPorts (machine regs a) b).regs
  have ha : embedState smallRegs emitPorts (machine regs a)
      (Squarefree.Program.prependData (regs ∘ smallRegs) key.reverse coeff.reverse a.framed) =
        machine regs a := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective emitPorts_injective
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [machine,tapes,Squarefree.Program.prependData,emitPorts,hk,hc]
    · intros; rfl
  have hb : embedState smallRegs emitPorts (machine regs a) b =
      machine rf {a with newkey:=[],coeff:=[], framed:=Encoding.frame key++Encoding.frame coeff++a.framed} := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective emitPorts_injective
    · intro i; exact embedState_register smallRegs emitPorts (machine regs a) b smallRegs_injective i
    · intro i hi; exact embedState_register_frame smallRegs emitPorts (machine regs a) b i hi
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> simp_all [emitPorts,machine,tapes,Fin.exists_fin_succ]
  have h := eval_call_lifted Squarefree.Program.prependRecordProgram smallRegs emitPorts
    (machine regs a) smallRegs_injective emitPorts_injective hh
  exact ⟨rf,by simpa only [ha,hb,emit,b] using h⟩

theorem compare_eval (regs : Fin 5 → Bool) (a : Tape) (key query : List Bool)
    (hk : a.key = key.reverse) (hq : a.target = query.reverse)
    (ht : a.tmp = []) (ht2 : a.tmp2 = []) :
    ∃ time ≤ 11*key.length+9*query.length+21, ∃ rf,
      Eval compare time (machine regs a) (machine rf {a with key:=[],tmp:=[],tmp2:=[]}) ∧
      rf 4 = decide (key=query) := by
  obtain ⟨time,htime,rr,hh,heq⟩ := Squarefree.Program.compareDictionaryKey_eval regs
    a.input key query a.output
  have ha : embedState id comparePorts (machine regs a)
      (SubexpRecordScan.recordState regs a.input key.reverse query.reverse [] [] a.output) =
        machine regs a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id comparePorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i <;> simp [machine,tapes,comparePorts,hk,hq,ht,ht2]
    · intros; rfl
  have hb : embedState id comparePorts (machine regs a)
      (SubexpRecordScan.recordState rr a.input [] query.reverse [] [] a.output) =
        machine rr {a with key:=[],tmp:=[],tmp2:=[]} := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id comparePorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i <;> simp [machine,tapes,comparePorts,hq]
    · intro i hi; fin_cases i <;> simp_all [comparePorts,machine,tapes,Fin.exists_fin_succ]
  have h := eval_liftCommand hh 0 5 id comparePorts (machine regs a)
    Function.injective_id comparePorts_injective
  refine ⟨time+1,by omega,rr,?_,heq⟩
  simpa only [ha,hb,compare] using h

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram


namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Copy one unary field to the reversed output key, including its delimiter. -/
theorem header_eval (regs : Fin 5 → Bool) (a : Tape) (n : ℕ) (rest : List Bool)
    (hw : a.work = Encoding.encodeNat n ++ rest) :
    ∃ rf, Eval header (4*n+5) (machine regs a)
      (machine rf {a with work:=rest,newkey:=(Encoding.encodeNat n).reverse++a.newkey}) := by
  let r := readRegs regs (0:Fin 5) 1 (some false)
  let b : Tape := {a with work:=rest,newkey:=List.replicate n true++a.newkey}
  have h := Squarefree.Program.readNat_eval (machine regs a) 4 5 (by decide) n rest hw
  have h' : Eval (Squarefree.Program.readNat 4 5) (4*n+4)
      (machine regs a) (machine r b) := by
    convert h using 1
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [machine,tapes,b]
  have hp := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (5:Fin 10) (0:Fin 5))
    (machine r b))
  have hp' : Eval (.base (.atom (.push 5 0))) 1 (machine r b)
      (machine r {a with work:=rest,newkey:=(Encoding.encodeNat n).reverse++a.newkey}) := by
    convert hp using 1
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;>
        simp [machine,tapes,b,r,Encoding.encodeNat,
          StructuredProgram.Atom.instr,execInstr,readRegs,List.reverse_append]
  refine ⟨r,?_⟩
  simpa [header] using h'.seq hp'

/-- The key rewriter reads the two unary fields and then scans precisely the mask. -/
theorem rewriteKey_eval (regs : Fin 5 → Bool) (a : Tape) (u z : ℕ) (mask : List Bool)
    (hk : a.key = (Encoding.encodeNat u++Encoding.encodeNat z++mask).reverse)
    (hw : a.work = []) (hn : a.newkey = []) :
    ∃ rf, Eval rewriteKey
      (3*(Encoding.encodeNat u++Encoding.encodeNat z++mask).length+4*u+4*z+6*mask.length+16)
      (machine regs a)
      (machine rf {a with work:=[],key:=mask.reverse, newkey:=(Encoding.encodeNat u++Encoding.encodeNat z++List.replicate mask.length false).reverse}) := by
  let a₁ : Tape := {a with key:=[],work:=Encoding.encodeNat u++Encoding.encodeNat z++mask}
  let r₁ := readRegs regs (0:Fin 5) 1 none
  have h₁ := transfer_machine regs a a₁ 2 4 (by decide) (by
    funext i; fin_cases i <;> simp [StackRoutines.transferStacks,tapes,a₁,hk,hw])
  obtain ⟨r₂,h₂⟩ := header_eval r₁ a₁ u (Encoding.encodeNat z++mask) (by simp [a₁,List.append_assoc])
  let a₂ : Tape := {a₁ with work:=Encoding.encodeNat z++mask,newkey:=(Encoding.encodeNat u).reverse++a₁.newkey}
  obtain ⟨r₃,h₃⟩ := header_eval r₂ a₂ z mask rfl
  let a₃ : Tape := {a₂ with work:=mask,newkey:=(Encoding.encodeNat z).reverse++a₂.newkey}
  obtain ⟨rf,h₄⟩ := scanMask_eval r₃ a₃
  have h₂' : Eval header (4*u+5) (machine r₁ a₁) (machine r₂ a₂) := h₂
  have h₃' : Eval header (4*z+5) (machine r₂ a₂) (machine r₃ a₃) := h₃
  have h₄' : Eval scanMask (6*mask.length+3) (machine r₃ a₃)
      (machine rf {a with work:=[],key:=mask.reverse, newkey:=(Encoding.encodeNat u++Encoding.encodeNat z++List.replicate mask.length false).reverse}) := by
    simpa [a₃,a₂,a₁,hn,List.reverse_append,List.append_assoc] using h₄
  refine ⟨rf,?_⟩
  have he := h₁.seq (h₂'.seq (h₃'.seq h₄'))
  convert he using 1 ; simp [tapes,hk,List.length_reverse] ; omega

/-- A successful record is prepended to the reversed accumulator. -/
theorem hit_eval (regs : Fin 5 → Bool) (a : Tape) (key coeff : List Bool)
    (hk : a.newkey = key.reverse) (hc : a.coeff = coeff.reverse) (hf : a.framed = []) :
    ∃ rf, Eval hit (4*key.length+4*coeff.length+13+
        (3*(Encoding.frame key++Encoding.frame coeff).length+3))
      (machine regs a)
      (machine rf {a with newkey:=[],coeff:=[],framed:=[], output:=(Encoding.frame key++Encoding.frame coeff).reverse++a.output}) := by
  obtain ⟨r₁,h₁⟩ := emit_eval regs a key coeff hk hc
  let b : Tape := {a with newkey:=[],coeff:=[],framed:=Encoding.frame key++Encoding.frame coeff}
  let c : Tape := {a with newkey:=[],coeff:=[],framed:=[], output:=(Encoding.frame key++Encoding.frame coeff).reverse++a.output}
  have h₁' : Eval emit (4*key.length+4*coeff.length+13) (machine regs a) (machine r₁ b) := by
    simpa [b,hf] using h₁
  have h₂ := transfer_machine r₁ b c 9 8 (by decide) (by
    funext i; fin_cases i <;> simp [StackRoutines.transferStacks,tapes,b,c])
  refine ⟨readRegs r₁ 0 1 none,?_⟩
  simpa [hit,b,tapes,c] using h₁'.seq h₂

theorem miss_eval (regs : Fin 5 → Bool) (a : Tape) :
    ∃ rf, Eval miss (2*a.coeff.length+3+(2*a.newkey.length+3))
      (machine regs a) (machine rf {a with coeff:=[],newkey:=[]}) := by
  let b : Tape := {a with coeff:=[]}
  let c : Tape := {a with coeff:=[],newkey:=[]}
  have h₁ := clear_machine regs a b 3 (by funext i; fin_cases i <;> simp [tapes,b])
  have h₂ := clear_machine (readRegs regs 0 1 none) b c 5
    (by funext i; fin_cases i <;> simp [tapes,b,c])
  refine ⟨readRegs (readRegs regs 0 1 none) 0 1 none,?_⟩
  simpa [miss,tapes,b,c] using h₁.seq h₂

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram


namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- All scratch tapes are empty at a record boundary. -/
def clean (source query output : List Bool) : Tape :=
  { input:=source,target:=query.reverse,output:=output }

def keyBits (u z : ℕ) (mask : List Bool) : List Bool :=
  Encoding.encodeNat u++Encoding.encodeNat z++mask

def recordBits (u z : ℕ) (mask coeff : List Bool) : List Bool :=
  Encoding.frame (keyBits u z mask)++Encoding.frame coeff

@[simp] theorem keyBits_length (u z : ℕ) (mask : List Bool) :
    (keyBits u z mask).length = u+z+mask.length+2 := by
  simp [keyBits,Encoding.encodeNat]; omega
@[simp] theorem recordBits_length (u z : ℕ) (mask coeff : List Bool) :
    (recordBits u z mask coeff).length = 2*(u+z+mask.length+coeff.length)+6 := by
  simp [recordBits,keyBits_length]; omega

theorem read_key (regs : Fin 5 → Bool) (u z : ℕ) (mask coeff rest query output : List Bool) :
    Eval (readFrame 0 2) (6*(keyBits u z mask).length+4)
      (machine regs (clean (recordBits u z mask coeff++rest) query output))
      (machine (readRegs regs 0 1 (some false))
        {clean (Encoding.frame coeff++rest) query output with key:=(keyBits u z mask).reverse}) := by
  have h := readFrame_eval (machine regs (clean (recordBits u z mask coeff++rest) query output))
    0 2 (by decide) (keyBits u z mask) (Encoding.frame coeff++rest)
    (by simp [machine,tapes,clean,recordBits,List.append_assoc])
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [machine,tapes,clean]

theorem read_coeff (regs : Fin 5 → Bool) (key coeff rest query output : List Bool) :
    Eval (readFrame 0 3) (6*coeff.length+4)
      (machine regs {clean (Encoding.frame coeff++rest) query output with key:=key})
      (machine (readRegs regs 0 1 (some false))
        {clean rest query output with key:=key,coeff:=coeff.reverse}) := by
  have h := readFrame_eval
    (machine regs {clean (Encoding.frame coeff++rest) query output with key:=key})
    0 3 (by decide) coeff rest rfl
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [machine,tapes,clean]

/-- One dictionary record is filtered by exact equality of its support mask. -/
theorem record_eval (regs : Fin 5 → Bool) (u z : ℕ)
    (mask coeff rest query output : List Bool) :
    ∃ time ≤ 100*((recordBits u z mask coeff).length+query.length+1), ∃ rf,
      Eval record time
        (machine regs (clean (recordBits u z mask coeff++rest) query output))
        (machine rf (clean rest query
          (if mask=query then (recordBits u z (List.replicate mask.length false) coeff).reverse++output
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
    simpa [a, b, keyBits, clean] using h₃
  obtain ⟨tc,htc,r₄,h₄,hr₄⟩ := compare_eval r₃ b mask query rfl rfl rfl rfl
  let c : Tape := {clean rest query output with coeff:=coeff.reverse, newkey:=(keyBits u z (List.replicate mask.length false)).reverse}
  have h₄' : Eval compare tc (machine r₃ b) (machine r₄ c) := by
    simpa [b, c, clean] using h₄
  by_cases heq : mask=query
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

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram


namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

structure Entry where
  u : ℕ
  z : ℕ
  mask : List Bool
  coeff : List Bool

def Entry.bits (e : Entry) : List Bool := recordBits e.u e.z e.mask e.coeff
def Entry.erased (e : Entry) : Entry := {e with mask:=List.replicate e.mask.length false}
def raw : List Entry → List Bool
  | [] => []
  | e::es => e.bits++raw es
def selected (query : List Bool) : List Entry → List Entry
  | [] => []
  | e::es => if e.mask=query then e.erased::selected query es else selected query es

def loopBudget (query : List Bool) : List Entry → ℕ
  | [] => 1
  | e::es => 100*(e.bits.length+query.length+1)+2+loopBudget query es

def readyRecords (regs : Fin 5 → Bool) (source query output : List Bool) : State 5 10 :=
  machine (readRegs regs 0 3 source.head?) (clean source query output)

@[simp] theorem readyRecords_guard (regs : Fin 5 → Bool) (source query output : List Bool) :
    (readyRecords regs source query output).regs 3 = !source.isEmpty := by
  cases source <;> simp [readyRecords,machine,readRegs]

@[simp] theorem raw_cons_ne (e : Entry) (es : List Entry) : raw (e::es) ≠ [] := by
  intro h
  have := congrArg List.length h
  simp [raw,Entry.bits,recordBits_length] at this

theorem readyRecords_cons_guard (regs : Fin 5 → Bool) (e : Entry)
    (es : List Entry) (query output : List Bool) :
    (readyRecords regs (raw (e::es)) query output).regs 3 = true := by
  cases hkey : keyBits e.u e.z e.mask <;>
    simp [readyRecords,machine,readRegs,raw,Entry.bits,recordBits,hkey,Encoding.frame]

/-- The dictionary traversal is a genuine while loop, with one pass over each record. -/
theorem records_eval (es : List Entry) (regs : Fin 5 → Bool) (query output : List Bool) :
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
        e.u e.z e.mask e.coeff (raw es) query output
      let out := if e.mask=query then e.erased.bits.reverse++output else output
      have hr' : Eval record tr (readyRecords regs (raw (e::es)) query output)
          (machine rr (clean (raw es) query out)) := by
        simpa [raw, readyRecords, out, Entry.erased, Entry.bits, machine, clean] using hr
      have hp : Eval (.base (.atom (.peek 0 0 3))) 1
          (machine rr (clean (raw es) query out)) (readyRecords rr (raw es) query out) :=
        Eval.base (StructuredProgram.Eval.atom _ _)
      obtain ⟨tt,htt,rf,ht⟩ := ih rr out
      have hall := Eval.while_true (body:=recordBody)
        (readyRecords_cons_guard regs e es query output) (hr'.seq hp) ht
      refine ⟨tr+1+tt+1,?_,rf,?_⟩
      · dsimp [loopBudget]; change tr ≤ _ at htr
        simpa [Entry.bits] using (show tr+1+tt+1 ≤
          100*((recordBits e.u e.z e.mask e.coeff).length+query.length+1)+2+loopBudget query es by omega)
      · by_cases h : e.mask=query <;>
          simpa only [selected,h,ite_true,ite_false,raw,out,Entry.bits,Entry.erased,
            List.reverse_append,List.append_assoc] using hall

theorem loopBudget_bound (query : List Bool) (es : List Entry) :
    loopBudget query es ≤ 102*((raw es).length+(query.length+1)*es.length)+1 := by
  induction es with
  | nil => simp [loopBudget,raw]
  | cons e es ih =>
      simp only [loopBudget,raw,List.length_append,List.length_cons]
      nlinarith

theorem raw_count (es : List Entry) : es.length ≤ (raw es).length := by
  induction es with
  | nil => simp [raw]
  | cons e es ih =>
      simp only [raw,List.length_append,List.length_cons]
      have he : 1 ≤ e.bits.length := by simp [Entry.bits,recordBits_length]
      omega

theorem selected_length (query : List Bool) (es : List Entry) :
    (raw (selected query es)).length ≤ (raw es).length := by
  induction es with
  | nil => simp [selected,raw]
  | cons e es ih =>
      by_cases h : e.mask=query
      · simp [selected,h,raw,Entry.erased,Entry.bits,recordBits_length] at *;omega
      · simp [selected,h,raw];omega

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram


/-! A fixed finite program for exact-support projection of a raw sparse dictionary.
Coefficients are opaque framed payloads. No normalization or arithmetic is used. -/
namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Serialized target-mask and dictionary input. -/
def input (query : List Bool) (es : List Entry) := Encoding.frame query++raw es

theorem project_eval (regs : Fin 5 → Bool) (query : List Bool) (es : List Entry) :
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
  obtain ⟨tt,htt,rr,ht⟩ := records_eval es r₁ query []
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
theorem serializedEval (regs : Fin 5 → Bool) (query : List Bool) (es : List Entry) :
    ∃ rf, RunsIn program (200*((raw es).length+1)*(query.length+2)+1)
      ((machine regs {input:=input query es}).withPC (some program.entry))
      ((machine rf {target:=query.reverse,framed:=raw (selected query es)}).withPC none) := by
  obtain ⟨time,htime,rf,h⟩ := project_eval regs query es
  exact ⟨rf,time+1,Nat.add_le_add_right htime 1,compiled_halt_trace h 0 9⟩

/-- The native program lowers to the primitive bit-machine with only its fixed
instruction-table overhead. The dictionary size already includes coefficient bits. -/
theorem primitive_serializedEval (query : List Bool) (es : List Entry) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program*(200*((raw es).length+1)*(query.length+2)+1))
      (primitiveCfg program ((machine (fun _ => false) {input:=input query es}).withPC
        (some program.entry)))
      (primitiveCfg program ((machine rf {target:=query.reverse, framed:=raw (selected query es)}).withPC none)) := by
  obtain ⟨rf,h⟩ := serializedEval (fun _ => false) query es
  exact ⟨rf,BitProgram.primitive_execution program h⟩

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram

end OAI.Algorithms
