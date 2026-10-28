import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.ModularRingPrograms
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgramStorage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramModel

namespace OAI.Algorithms


/-! A fixed scanner widens consecutive two-bit coefficients using a runtime
width tape. The original width is preserved, and all bit movement is paid. -/
namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ModularPrograms
open SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev Data := State 8 7
abbrev Code := Cmd 8 7

def tapes (input width shape word output temp final : List Bool) : Fin 7 → List Bool :=
  ![input,width,shape,word,output,temp,final]
def state (regs : Fin 8 → Bool) (input width shape word output temp final : List Bool) : Data :=
  ⟨regs,tapes input width shape word output temp final⟩

def paddingPorts : Fin 3 → Fin 7 := ![2,3,4]
theorem paddingPorts_injective : Function.Injective paddingPorts := by decide

def pad : Code := .call (ProgramLinking.liftProgram paddingProgram id paddingPorts)

theorem pad_eval (regs : Fin 8 → Bool) (input width shape word output temp final : List Bool) :
    ∃ rf, Eval pad (4*shape.length+3)
      (state regs input width shape word output temp final)
      (state rf input width [] (word.drop shape.length)
        ((ModularArithmetic.padTo shape word).reverse ++ output) temp final) := by
  obtain ⟨rf,ht⟩ := ModularRingPrograms.paddingPrefix_correct regs shape word output
  let d := state regs input width shape word output temp final
  let a : State 8 3 := ⟨regs,operandStacks shape word output⟩
  let b : State 8 3 := ⟨rf,operandStacks [] (word.drop shape.length)
    ((ModularArithmetic.padTo shape word).reverse ++ output)⟩
  have ha : embedState id paddingPorts d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id paddingPorts_injective
    · intro i; rfl
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hb : embedState id paddingPorts d b = state rf input width [] (word.drop shape.length)
      ((ModularArithmetic.padTo shape word).reverse ++ output) temp final := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id paddingPorts_injective
    · intro i; rfl
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro j hj
      fin_cases j <;> try rfl
      · exact False.elim (hj ⟨0,rfl⟩)
      · exact False.elim (hj ⟨1,rfl⟩)
      · exact False.elim (hj ⟨2,rfl⟩)
  have ht' : Trace paddingProgram (4*shape.length+3)
      (a.withPC (some paddingProgram.entry)) (b.withPC none) := ht
  have h := eval_call_lifted paddingProgram id paddingPorts d
    Function.injective_id paddingPorts_injective ht'
  exact ⟨rf,by simpa only [ha,hb,pad] using h⟩

def takeTwo : Code := .seq (.base (.atom (.pop 0 0 6)))
  (.seq (.base (.atom (.pop 0 1 6)))
    (.seq (.base (.atom (.push 3 1))) (.base (.atom (.push 3 0)))))

theorem popInput_eval (regs : Fin 8 → Bool) (r : Fin 8) (bit : Bool)
    (input width shape word output temp final : List Bool) :
    Eval (.base (.atom (.pop 0 r 6))) 1
      (state regs (bit::input) width shape word output temp final)
      (state (readRegs regs r 6 (some bit)) input width shape word output temp final) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 8) (s := 7) 0 r 6)
    (state regs (bit::input) width shape word output temp final) using 1
  all_goals
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;>
        simp [state,tapes,StructuredProgram.Atom.instr,execInstr]

theorem pushWord_eval (regs : Fin 8 → Bool) (r : Fin 8)
    (input width shape word output temp final : List Bool) :
    Eval (.base (.atom (.push 3 r))) 1
      (state regs input width shape word output temp final)
      (state regs input width shape (regs r::word) output temp final) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 8) (s := 7) 3 r)
    (state regs input width shape word output temp final) using 1
  all_goals
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;>
        simp [state,tapes,StructuredProgram.Atom.instr,execInstr]

theorem takeTwo_eval (regs : Fin 8 → Bool) (a b : Bool)
    (input width shape output temp final : List Bool) :
    ∃ rf, Eval takeTwo 4 (state regs (a::b::input) width shape [] output temp final)
      (state rf input width shape [a,b] output temp final) := by
  let r1 := readRegs regs 0 6 (some a)
  let r2 := readRegs r1 1 6 (some b)
  have h1 := popInput_eval regs 0 a (b::input) width shape [] output temp final
  have h2 := popInput_eval r1 1 b input width shape [] output temp final
  have h3 := pushWord_eval r2 1 input width shape [] output temp final
  have h4 := pushWord_eval r2 0 input width shape [b] output temp final
  have hb : r2 1=b := by simp [r2,readRegs]
  have ha : r2 0=a := by simp [r2,r1,readRegs]
  rw [hb] at h3
  rw [ha] at h4
  exact ⟨r2,h1.seq (h2.seq (h3.seq h4))⟩

def step : Code := .seq takeTwo (.seq (copy 1 2 5) pad)

theorem step_eval (regs : Fin 8 → Bool) (word input width output final : List Bool)
    (hword : word.length=2) (hwidth : 2 ≤ width.length) :
    ∃ rf, Eval step (11*width.length+12)
      (state regs (word++input) width [] [] output [] final)
      (state rf input width [] [] ((ModularArithmetic.padTo width word).reverse++output) [] final) := by
  obtain ⟨a,b,rfl⟩ : ∃ a b, word=[a,b] := by
    cases word with
    | nil => simp at hword
    | cons a word =>
      cases word with
      | nil => simp at hword
      | cons b word =>
        have hw : word=[] := List.length_eq_zero_iff.mp (by simpa using hword)
        exact ⟨a,b,by simp [hw]⟩
  obtain ⟨r1,h1⟩ := takeTwo_eval regs a b input width [] output [] final
  obtain ⟨s2,h2,hs2⟩ := copy_eval (1 : Fin 7) 2 5 (by decide) (by decide) (by decide)
    (state r1 input width [] [a,b] output [] final) rfl
  have hstate : s2=state s2.regs input width width [a,b] output [] final := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · rw [hs2]; funext i; fin_cases i <;> simp [state,tapes,StackRoutines.copyStacks]
  rw [hstate] at h2
  obtain ⟨rf,h3⟩ := pad_eval s2.regs input width width [a,b] output [] final
  have hd : [a,b].drop width.length=[] := List.drop_eq_nil_of_le (by simpa using hwidth)
  rw [hd] at h3
  have he := h1.seq (h2.seq h3)
  have hc : 4+((7*width.length+5)+(4*width.length+3))=11*width.length+12 := by omega
  refine ⟨rf,?_⟩
  simpa only [step, state, tapes, Matrix.cons_val_one, Matrix.cons_val_zero,
    List.cons_append, List.nil_append, hc] using he

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram


namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

/-- The word list is a specification value; the machine scans its flat tape. -/
def padded (width : List Bool) (words : List (List Bool)) : List Bool :=
  (words.map (ModularArithmetic.padTo width)).flatten

@[simp] theorem padded_nil (width : List Bool) : padded width []=[] := rfl
@[simp] theorem padded_cons (width word : List Bool) (words : List (List Bool)) :
    padded width (word::words)=ModularArithmetic.padTo width word++padded width words := rfl
@[simp] theorem padded_length (width : List Bool) (words : List (List Bool)) :
    (padded width words).length=words.length*width.length := by
  induction words with
  | nil => simp
  | cons w ws ih => simp [ih,Nat.add_mul,Nat.add_comm,ModularArithmetic.padTo_length]

def peek : Code := .base (.atom (.peek 0 0 7))
def loop : Code := .while 7 (.seq step peek)
def scan : Code := .seq peek loop

theorem peek_eval (regs : Fin 8 → Bool) (input width output final : List Bool) :
    Eval peek 1 (state regs input width [] [] output [] final)
      (state (readRegs regs 0 7 input.head?) input width [] [] output [] final) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.peek (r := 8) (s := 7) 0 0 7)
    (state regs input width [] [] output [] final) using 1 ;
    simp [state,tapes,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr]

theorem loop_eval (words : List (List Bool)) (width : List Bool)
    (hwords : ∀ w ∈ words, w.length=2) (hwidth : 2 ≤ width.length)
    (regs : Fin 8 → Bool) (output final : List Bool) :
    ∃ rf, Eval loop (words.length*(11*width.length+14)+1)
      (state (readRegs regs 0 7 words.flatten.head?) words.flatten width [] [] output [] final)
      (state rf [] width [] [] ((padded width words).reverse++output) [] final) := by
  induction words generalizing regs output with
  | nil =>
    refine ⟨readRegs regs 0 7 none,?_⟩
    simp only [List.length_nil,Nat.zero_mul,Nat.zero_add,List.flatten_nil,
      List.head?_nil,padded_nil,List.reverse_nil,List.nil_append]
    apply Eval.while_false
    simp [state,readRegs_present]
  | cons word words ih =>
    have hw := hwords word (by simp)
    obtain ⟨a,b,rfl⟩ : ∃ a b, word=[a,b] := by
      cases word with
      | nil => simp at hw
      | cons a word =>
        cases word with
        | nil => simp at hw
        | cons b word =>
          have hz : word=[] := List.length_eq_zero_iff.mp (by simpa using hw)
          exact ⟨a,b,by simp [hz]⟩
    obtain ⟨r1,h1⟩ := step_eval (readRegs regs 0 7 (some a)) [a,b] words.flatten width output final
      rfl hwidth
    have h2 := peek_eval r1 words.flatten width
      ((ModularArithmetic.padTo width [a,b]).reverse++output) final
    obtain ⟨rf,h3⟩ := ih (fun w hw => hwords w (by simp [hw])) r1
      ((ModularArithmetic.padTo width [a,b]).reverse++output)
    have h := Eval.while_true
      (show (state (readRegs regs 0 7 (some a)) ([a,b]++words.flatten)
        width [] [] output [] final).regs 7=true by simp [state,readRegs_present])
      (h1.seq h2) h3
    have hc : (11*width.length+12)+1+(words.length*(11*width.length+14)+1)+1=
        (words.length+1)*(11*width.length+14)+1 := by ring
    rw [hc] at h
    refine ⟨rf,?_⟩
    simpa only [loop,List.length_cons,List.flatten_cons,List.head?_cons,List.cons_append,
      List.nil_append,padded_cons,List.reverse_append,List.append_assoc] using h

theorem scan_eval (words : List (List Bool)) (width : List Bool)
    (hwords : ∀ w ∈ words, w.length=2) (hwidth : 2 ≤ width.length)
    (regs : Fin 8 → Bool) (output final : List Bool) :
    ∃ rf, Eval scan (words.length*(11*width.length+14)+2)
      (state regs words.flatten width [] [] output [] final)
      (state rf [] width [] [] ((padded width words).reverse++output) [] final) := by
  have h1 := peek_eval regs words.flatten width output final
  obtain ⟨rf,h2⟩ := loop_eval words width hwords hwidth regs output final
  have h := h1.seq h2
  have hc : 1+(words.length*(11*width.length+14)+1)=words.length*(11*width.length+14)+2 := by omega
  rw [hc] at h
  exact ⟨rf,h⟩

def command : Code := .seq scan (transfer 4 6)
def program := compiled command 0 6

theorem command_eval (words : List (List Bool)) (width : List Bool)
    (hwords : ∀ w ∈ words, w.length=2) (hwidth : 2 ≤ width.length)
    (regs : Fin 8 → Bool) :
    ∃ rf, Eval command (words.length*(14*width.length+14)+5)
      (state regs words.flatten width [] [] [] [] [])
      (state rf [] width [] [] [] [] (padded width words)) := by
  obtain ⟨r1,h1⟩ := scan_eval words width hwords hwidth regs [] []
  simp only [List.append_nil] at h1
  obtain ⟨e,h2,hs⟩ := transfer_eval (4 : Fin 7) 6 (by decide)
    (state r1 [] width [] [] (padded width words).reverse [] [])
  have he : e=state e.regs [] width [] [] [] [] (padded width words) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · rw [hs]; funext i; fin_cases i <;>
        simp [state,tapes,StackRoutines.transferStacks]
  rw [he] at h2
  have hlen : ((state r1 [] width [] [] (padded width words).reverse [] []).stacks 4).length =
      words.length*width.length := by
    change (padded width words).reverse.length=_
    rw [List.length_reverse,padded_length]
  rw [hlen] at h2
  have h := h1.seq h2
  have hc : (words.length*(11*width.length+14)+2)+(3*(words.length*width.length)+3)=
      words.length*(14*width.length+14)+5 := by ring
  rw [hc] at h
  exact ⟨e.regs,h⟩

theorem program_trace (words : List (List Bool)) (width : List Bool)
    (hwords : ∀ w ∈ words, w.length=2) (hwidth : 2 ≤ width.length)
    (regs : Fin 8 → Bool) :
    ∃ rf, Trace program (words.length*(14*width.length+14)+6)
      ((state regs words.flatten width [] [] [] [] []).withPC (some program.entry))
      ((state rf [] width [] [] [] [] (padded width words)).withPC none) := by
  obtain ⟨rf,h⟩ := command_eval words width hwords hwidth regs
  exact ⟨rf,by simpa [program,Nat.add_assoc] using compiled_halt_trace h 0 6⟩

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram


/-! Exact byte bridge from canonical F3 coefficients to the supplied-polynomial
ring model. The program itself has no degree or width parameter. -/
namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.ModularArithmetic

 theorem pad_coefficient (t : ℕ) (ht : 0 < t) (a : ZMod 3) (width : List Bool)
    (hw : width.length=baseWidth 3 t) :
    padTo width (IrreducibleSearchProgram.coefficientWord a)=
      (RingProgram.liftCoefficientRun t a).1.val := by
  apply SubexponentialSAT.SubexpModulusConstruction.bits_eq_of_length_of_value
  · rw [padTo_length, hw]
    exact (RingProgram.liftCoefficientRun t a).1.property.symm
  · rw [ModularRingPrograms.padTo_value_of_lt,RingProgram.liftCoefficientRun_value t ht]
    · exact SubexpEnumerationPayload.scalarBits_value a
    · change BinaryArithmetic.toNat (SubexpEnumerationPayload.scalarBits a) < 2^width.length
      rw [SubexpEnumerationPayload.scalarBits_value,hw,RingProgram.ternary_baseWidth]
      have hp := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) (show 2 ≤ 2*t by omega)
      have ha := a.val_lt
      norm_num at hp
      omega

theorem padded_coefficients (t : ℕ) (ht : 0 < t) (as : List (ZMod 3)) (width : List Bool)
    (hw : width.length=baseWidth 3 t) :
    padded width (as.map IrreducibleSearchProgram.coefficientWord)=
      (as.map (fun a => (RingProgram.liftCoefficientRun t a).1.val)).flatten := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [padded_cons,pad_coefficient t ht a width hw,ih]

theorem padded_ofFn (t : ℕ) (ht : 0 < t) {d : ℕ} (as : Fin d → ZMod 3)
    (width : List Bool) (hw : width.length=baseWidth 3 t) :
    padded width ((List.ofFn as).map IrreducibleSearchProgram.coefficientWord)=
      RingProgram.flat (RingProgram.liftCoefficientsRun t as).1 := by
  rw [padded_coefficients t ht _ width hw]
  simp only [RingProgram.flat,RingProgram.liftCoefficientsRun,RingProgram.tabulateRun_eq,
    List.map_ofFn]
  rfl

theorem coefficients_eval (t : ℕ) (ht : 0 < t) {d : ℕ} (as : Fin d → ZMod 3)
    (width : List Bool) (hw : width.length=baseWidth 3 t) (regs : Fin 8 → Bool) :
    ∃ rf, Eval command (d*(28*t+14)+5)
      (state regs (IrreducibleSearchProgram.coefficientArray (List.ofFn as)) width [] [] [] [] [])
      (state rf [] width [] [] [] [] (RingProgram.flat (RingProgram.liftCoefficientsRun t as).1)) := by
  have hw2 : 2 ≤ width.length := by rw [hw,RingProgram.ternary_baseWidth]; omega
  obtain ⟨rf,h⟩ := command_eval ((List.ofFn as).map IrreducibleSearchProgram.coefficientWord)
    width (by intro w hw; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
              exact IrreducibleSearchProgram.coefficientWord_length a) hw2 regs
  rw [padded_ofFn t ht as width hw] at h
  have hc : ((List.ofFn as).map IrreducibleSearchProgram.coefficientWord).length*
      (14*width.length+14)+5=d*(28*t+14)+5 := by
    simp only [List.length_map,List.length_ofFn,hw,RingProgram.ternary_baseWidth]
    ring
  rw [hc] at h
  exact ⟨rf,by simpa only [IrreducibleSearchProgram.coefficientArray_flatten] using h⟩

theorem coefficients_trace (t : ℕ) (ht : 0 < t) {d : ℕ} (as : Fin d → ZMod 3)
    (width : List Bool) (hw : width.length=baseWidth 3 t) (regs : Fin 8 → Bool) :
    ∃ rf, Trace program (d*(28*t+14)+6)
      ((state regs (IrreducibleSearchProgram.coefficientArray (List.ofFn as)) width [] [] [] [] []).withPC
        (some program.entry))
      ((state rf [] width [] [] [] [] (RingProgram.flat (RingProgram.liftCoefficientsRun t as).1)).withPC none) := by
  obtain ⟨rf,h⟩ := coefficients_eval t ht as width hw regs
  exact ⟨rf,by simpa [program,Nat.add_assoc] using compiled_halt_trace h 0 6⟩

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram


/-! Search-to-table ABI. The search has 22 registers and 28 stacks. In particular,
stack24 may contain unread candidates and is outside this adapter's ports. -/
namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev SearchData := State 22 28

def searchRegisters : Fin 8 → Fin 22 := Fin.castAdd 14
def searchPorts : Fin 7 → Fin 28 := ![13,12,23,15,25,26,21]
theorem searchRegisters_injective : Function.Injective searchRegisters := Fin.castAdd_injective _ _
theorem searchPorts_injective : Function.Injective searchPorts := by decide

abbrev searchCommand : Cmd 22 28 := liftCommand command 0 6 searchRegisters searchPorts
def searchProgram := compiled searchCommand 13 21

def SearchReady (s : SearchData) : Prop :=
  s.stacks 23=[] ∧ s.stacks 15=[] ∧ s.stacks 25=[] ∧ s.stacks 26=[] ∧ s.stacks 21=[]

/-- The polynomial input appears on21, source13 is consumed, and all other
stacks (including the runtime width12, degree14, counts22 and candidates24)
are preserved. The exact result is the ring model's coefficient code. -/
theorem searchCommand_eval (t : ℕ) (ht : 0 < t) {d : ℕ} (as : Fin d → ZMod 3)
    (s : SearchData) (hready : SearchReady s)
    (hinput : s.stacks 13=IrreducibleSearchProgram.coefficientArray (List.ofFn as))
    (hwidth : (s.stacks 12).length=SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ e, Eval searchCommand (d*(28*t+14)+6) s e ∧
      e.stacks=Function.update (Function.update s.stacks 13 []) 21
        (RingProgram.flat (RingProgram.liftCoefficientsRun t as).1) ∧
      (∀ i, i ∉ Set.range searchRegisters → e.regs i=s.regs i) := by
  obtain ⟨h23,h15,h25,h26,h21⟩ := hready
  let a := projectState searchRegisters searchPorts s
  have ha : a=state a.regs (IrreducibleSearchProgram.coefficientArray (List.ofFn as))
      (s.stacks 12) [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [searchPorts,tapes,hinput,h23,h15,h25,h26,h21]
  obtain ⟨rf,h⟩ := coefficients_eval t ht as (s.stacks 12) hwidth a.regs
  rw [←ha] at h
  let b := state rf [] (s.stacks 12) [] [] [] []
    (RingProgram.flat (RingProgram.liftCoefficientsRun t as).1)
  let e := embedState searchRegisters searchPorts s b
  have he := eval_liftCommand_from_state command 0 6 searchRegisters searchPorts s
    searchRegisters_injective searchPorts_injective h
  have hb : b.stacks=Function.update (Function.update a.stacks 0 []) 6
      (RingProgram.flat (RingProgram.liftCoefficientsRun t as).1) := by
    rw [ha]
    funext i; fin_cases i <;> rfl
  refine ⟨e,?_,?_,?_⟩
  · simpa [searchCommand,Nat.add_assoc] using he
  · change Function.extend searchPorts b.stacks s.stacks=_
    rw [hb,ProgramLinking.extend_update searchPorts_injective,
      ProgramLinking.extend_update searchPorts_injective]
    have hbase := congrArg StructuredProgram.State.stacks
      (embedState_project searchRegisters searchPorts s searchRegisters_injective searchPorts_injective)
    change Function.extend searchPorts a.stacks s.stacks=s.stacks at hbase
    rw [hbase]
    rfl
  · intro i hi
    exact embedState_register_frame searchRegisters searchPorts s b i hi

theorem searchProgram_trace (t : ℕ) (ht : 0 < t) {d : ℕ} (as : Fin d → ZMod 3)
    (s : SearchData) (hready : SearchReady s)
    (hinput : s.stacks 13=IrreducibleSearchProgram.coefficientArray (List.ofFn as))
    (hwidth : (s.stacks 12).length=SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ e : SearchData, Trace searchProgram (d*(28*t+14)+7)
      (s.withPC (some searchProgram.entry)) (e.withPC none) ∧
      e.stacks=Function.update (Function.update s.stacks 13 []) 21
        (RingProgram.flat (RingProgram.liftCoefficientsRun t as).1) := by
  obtain ⟨e,h,hs,_⟩ := searchCommand_eval t ht as s hready hinput hwidth
  exact ⟨e,by simpa [searchProgram,Nat.add_assoc] using compiled_halt_trace h 13 21,hs⟩

/-- The corresponding single-bit primitive machine has a fixed overhead,
independent of both the runtime degree and the runtime coefficient width. -/
theorem searchProgram_primitive (t : ℕ) (ht : 0 < t) {d : ℕ} (as : Fin d → ZMod 3)
    (s : SearchData) (hready : SearchReady s)
    (hinput : s.stacks 13=IrreducibleSearchProgram.coefficientArray (List.ofFn as))
    (hwidth : (s.stacks 12).length=SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ e : SearchData, Computation.RunsIn (primitive searchProgram).step
      (primitiveOverhead searchProgram*(d*(28*t+14)+7))
      (primitiveCfg searchProgram (s.withPC (some searchProgram.entry)))
      (primitiveCfg searchProgram (e.withPC none)) ∧
      e.stacks=Function.update (Function.update s.stacks 13 []) 21
        (RingProgram.flat (RingProgram.liftCoefficientsRun t as).1) := by
  obtain ⟨e,h,hs⟩ := searchProgram_trace t ht as s hready hinput hwidth
  exact ⟨e,BitProgram.primitive_execution searchProgram ⟨_,le_rfl,h⟩,hs⟩

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram

end OAI.Algorithms
