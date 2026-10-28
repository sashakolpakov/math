import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFRecords
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-!
# Local encoded worklist updates by a fixed Boolean-stack program

The branch decision and child records are supplied as data. No formula search
or splitting callback is an instruction. Pending work, accumulated leaves, and
both child sources may have arbitrary suffixes; only the current records are
read. The five stack ports are pending, leaves, child A, child B, and scratch.
-/

namespace SubexponentialSAT.ExecWorklistProgram

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 4 5

/-- One tagged, escaped list record. The payload may encode a whole CNF. -/
def record (bits : List Bool) : List Bool := true :: Encoding.frame bits

@[simp] theorem record_length (bits : List Bool) : (record bits).length = 2 * bits.length + 2 := by
  simp [record, Encoding.length_frame]

private theorem extend_eq {α β γ : Type*} {f : α → β}
    (hf : Function.Injective f) (inner : α → γ) (frame target : β → γ)
    (hin : ∀ i, target (f i) = inner i)
    (hout : ∀ i, (¬ ∃ j, f j = i) → target i = frame i) :
    Function.extend f inner frame = target := by
  classical
  funext i
  by_cases hi : ∃ j, f j = i
  · obtain ⟨j,rfl⟩ := hi
    rw [hf.extend_apply]
    exact (hin j).symm
  · rw [Function.extend_apply' _ _ _ hi]
    exact (hout i hi).symm

private theorem embed_eq {r s R S : ℕ} (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (frame target : StructuredProgram.State R S) (inner : StructuredProgram.State r s)
    (hri : ∀ i, target.regs (reg i) = inner.regs i)
    (hro : ∀ i, (¬ ∃ j, reg j = i) → target.regs i = frame.regs i)
    (hsi : ∀ i, target.stacks (stk i) = inner.stacks i)
    (hso : ∀ i, (¬ ∃ j, stk j = i) → target.stacks i = frame.stacks i) :
    embedState reg stk frame inner = target := by
  have he₁ := extend_eq hr inner.regs frame.regs target.regs hri hro
  have he₂ := extend_eq hs inner.stacks frame.stacks target.stacks hsi hso
  cases target
  simp only [embedState, he₁, he₂]

def workRegs : Fin 2 → Fin 4 := ![0, 1]
def copyPorts (src dst : Fin 5) : Fin 3 → Fin 5 := ![src, dst, 4]

theorem workRegs_injective : Function.Injective workRegs := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [workRegs]

theorem copyPorts_injective (src dst : Fin 5)
    (hsd : src ≠ dst) (hst : src ≠ 4) (hdt : dst ≠ 4) :
    Function.Injective (copyPorts src dst) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [copyPorts]

/-- The three copy ports are fixed when this finite program is constructed. -/
abbrev copyAt (src dst : Fin 5) : Program 4 5 16 :=
  ProgramLinking.liftProgram ExecCNFRecords.copyProgram workRegs (copyPorts src dst)

def copyAfter (src dst : Fin 5) (bits rest : List Bool) (d : Data) : Data :=
  ⟨Function.update (Function.update d.regs 0 false) 1 false,
    Function.update (Function.update d.stacks src rest) dst (record bits ++ d.stacks dst)⟩

/-- A framed copy reads one record only, including when the source contains
more records. The exact trace is inherited from the actual fixed copy program. -/
theorem copyAt_eval (src dst : Fin 5)
    (hsd : src ≠ dst) (hst : src ≠ 4) (hdt : dst ≠ 4)
    (d : Data) (bits rest : List Bool)
    (hsrc : d.stacks src = record bits ++ rest) (htmp : d.stacks 4 = []) :
    Eval (.call (copyAt src dst)) (13 * bits.length + 18) d (copyAfter src dst bits rest d) := by
  let a : StructuredProgram.State 2 3 :=
    ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
      ExecCNFRecords.ports (record bits ++ rest) (d.stacks dst) []⟩
  let b : StructuredProgram.State 2 3 :=
    ⟨ParserProgram.pair false false, ExecCNFRecords.ports rest (record bits ++ d.stacks dst) []⟩
  have hr := workRegs_injective
  have hs := copyPorts_injective src dst hsd hst hdt
  have ha : embedState workRegs (copyPorts src dst) d a = d := by
    apply embed_eq _ _ hr hs
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
    · intro i; fin_cases i
      · exact hsrc
      · rfl
      · exact htmp
    · intro i hi; rfl
  have hb : embedState workRegs (copyPorts src dst) d b = copyAfter src dst bits rest d := by
    apply embed_eq _ _ hr hs
    · intro i; fin_cases i <;> simp [copyAfter, workRegs, b, ParserProgram.pair]
    · intro i hi
      have h0 : i ≠ 0 := by intro he; exact hi ⟨0, he.symm⟩
      have h1 : i ≠ 1 := by intro he; exact hi ⟨1, he.symm⟩
      simp [copyAfter, h0, h1]
    · intro i; fin_cases i <;>
        simp [copyAfter, copyPorts, b, hsd, hst.symm, hdt.symm, htmp]
    · intro i hi
      have hsrc' : i ≠ src := by intro he; exact hi ⟨0, he.symm⟩
      have hdst' : i ≠ dst := by intro he; exact hi ⟨1, he.symm⟩
      simp [copyAfter, hsrc', hdst']
  have ht : Trace ExecCNFRecords.copyProgram (13 * bits.length + 18)
      (a.withPC (some ExecCNFRecords.copyProgram.entry)) (b.withPC none) := by
    convert ExecCNFRecords.copy_record_trace bits rest (d.stacks dst) (d.regs 0) (d.regs 1) using 1 <;>
      simp [a, b, StructuredProgram.State.withPC, ExecCNFRecords.copyCfg, record,
        List.cons_append ]
  have he := eval_call_lifted ExecCNFRecords.copyProgram workRegs (copyPorts src dst) d hr hs ht
  rw [ha, hb] at he
  exact he

def skipRegs : Fin 3 → Fin 4 := ![0, 1, 3]
def skipPorts : Fin 1 → Fin 5 := fun _ => 0

theorem skipRegs_injective : Function.Injective skipRegs := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [skipRegs]

theorem skipPorts_injective : Function.Injective skipPorts := by
  intro i j h
  exact Subsingleton.elim _ _

abbrev skipAt : Program 4 5 11 :=
  ProgramLinking.liftProgram ExecCNFRecords.skipProgram skipRegs skipPorts

def skipAfter (rest : List Bool) (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 true) 3 true,
    Function.update d.stacks 0 rest⟩

theorem skipAt_eval (d : Data) (bits rest : List Bool)
    (hsrc : d.stacks 0 = record bits ++ rest) :
    Eval (.call skipAt) (5 * bits.length + 8) d (skipAfter rest d) := by
  let a : StructuredProgram.State 3 1 :=
    ⟨ExecCNFRecords.regs (d.regs 0) (d.regs 1) (d.regs 3), fun _ => record bits ++ rest⟩
  let b : StructuredProgram.State 3 1 := ⟨ExecCNFRecords.regs false true true, fun _ => rest⟩
  have hr := skipRegs_injective
  have hs := skipPorts_injective
  have ha : embedState skipRegs skipPorts d a = d := by
    apply embed_eq _ _ hr hs
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
    · intro i; fin_cases i; exact hsrc
    · intro i hi; rfl
  have hb : embedState skipRegs skipPorts d b = skipAfter rest d := by
    apply embed_eq _ _ hr hs
    · intro i; fin_cases i <;> simp [skipAfter, skipRegs, b, ExecCNFRecords.regs]
    · intro i hi
      have h0 : i ≠ 0 := by intro he; exact hi ⟨0, he.symm⟩
      have h1 : i ≠ 1 := by intro he; exact hi ⟨1, he.symm⟩
      have h3 : i ≠ 3 := by intro he; exact hi ⟨2, he.symm⟩
      simp [skipAfter, h0, h1, h3]
    · intro i; fin_cases i; simp [skipAfter, skipPorts, b]
    · intro i hi
      have h0 : i ≠ 0 := by intro he; exact hi ⟨0, he.symm⟩
      simp [skipAfter, h0]
  have ht : Trace ExecCNFRecords.skipProgram (5 * bits.length + 8)
      (a.withPC (some ExecCNFRecords.skipProgram.entry)) (b.withPC none) := by
    simpa only [a, b, StructuredProgram.State.withPC, ExecCNFRecords.cfg, record,
      List.cons_append] using ExecCNFRecords.record_trace bits rest (d.regs 0) (d.regs 1) (d.regs 3)
  have he := eval_call_lifted ExecCNFRecords.skipProgram skipRegs skipPorts d hr hs ht
  rw [ha, hb] at he
  exact he

/-- Register 2 is the supplied terminal decision; register 3 is the skip flag.
Every stack may contain an arbitrary suffix except for the empty local scratch. -/
abbrev data (terminal value present found : Bool)
    (pending leaves left right : List Bool) : Data :=
  ⟨![value, present, terminal, found], ![pending, leaves, left, right, []]⟩

private theorem data_ext (a b : Data) (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  simp_all

@[simp] theorem copyAfter_emit (terminal v p f : Bool)
    (bits rest leaves left right : List Bool) :
    copyAfter 0 1 bits rest (data terminal v p f (record bits ++ rest) leaves left right) =
      data terminal false false f rest (record bits ++ leaves) left right := by
  apply data_ext <;> funext i <;> fin_cases i <;> simp [copyAfter ]

@[simp] theorem copyAfter_right (terminal v p f : Bool)
    (bits rest pending leaves left : List Bool) :
    copyAfter 3 0 bits rest (data terminal v p f pending leaves left (record bits ++ rest)) =
      data terminal false false f (record bits ++ pending) leaves left rest := by
  apply data_ext <;> funext i <;> fin_cases i <;> simp [copyAfter ]

@[simp] theorem copyAfter_left (terminal v p f : Bool)
    (bits rest pending leaves right : List Bool) :
    copyAfter 2 0 bits rest (data terminal v p f pending leaves (record bits ++ rest) right) =
      data terminal false false f (record bits ++ pending) leaves rest right := by
  apply data_ext <;> funext i <;> fin_cases i <;> simp [copyAfter ]

@[simp] theorem skipAfter_data (terminal v p f : Bool)
    (rest pending leaves left right : List Bool) :
    skipAfter rest (data terminal v p f pending leaves left right) =
      data terminal false true true rest leaves left right := by
  apply data_ext <;> funext i <;> fin_cases i <;> simp [skipAfter ]

/-- Push B before A, putting A at the top of the depth-first pending stack. -/
abbrev branchCommand : Cmd 4 5 :=
  .seq (.call skipAt) (.seq (.call (copyAt 3 0)) (.call (copyAt 2 0)))

/-- Both branches consist exclusively of calls to fixed finite bit programs. -/
abbrev command : Cmd 4 5 := .ite 2 (.call (copyAt 0 1)) branchCommand

/-- Four Boolean registers, five Boolean stacks, and 61 fixed control labels.
These counts do not depend on payloads, formula width, or the number of leaves. -/
abbrev program := compiled command 0 1

theorem terminal_eval (bits rest leaves left right : List Bool) (v p f : Bool) :
    Eval command (13 * bits.length + 19)
      (data true v p f (record bits ++ rest) leaves left right)
      (data true false false f rest (record bits ++ leaves) left right) := by
  have hc := copyAt_eval 0 1 (by decide) (by decide) (by decide)
    (data true v p f (record bits ++ rest) leaves left right) bits rest rfl rfl
  rw [copyAfter_emit] at hc
  have h : Eval command ((13 * bits.length + 18) + 1)
      (data true v p f (record bits ++ rest) leaves left right)
      (data true false false f rest (record bits ++ leaves) left right) :=
    .ite_true rfl hc
  simpa only [Nat.add_assoc] using h

theorem branch_eval (current left right pending leaves leftRest rightRest : List Bool)
    (v p f : Bool) :
    Eval command (5 * current.length + 13 * right.length + 13 * left.length + 45)
      (data false v p f (record current ++ pending) leaves
        (record left ++ leftRest) (record right ++ rightRest))
      (data false false false true (record left ++ (record right ++ pending)) leaves leftRest rightRest) := by
  have hs := skipAt_eval (data false v p f (record current ++ pending) leaves
    (record left ++ leftRest) (record right ++ rightRest)) current pending rfl
  rw [skipAfter_data] at hs
  have hb := copyAt_eval 3 0 (by decide) (by decide) (by decide)
    (data false false true true pending leaves (record left ++ leftRest) (record right ++ rightRest))
    right rightRest rfl rfl
  rw [copyAfter_right] at hb
  have ha := copyAt_eval 2 0 (by decide) (by decide) (by decide)
    (data false false false true (record right ++ pending) leaves (record left ++ leftRest) rightRest)
    left leftRest rfl rfl
  rw [copyAfter_left] at ha
  have h : Eval command ((5 * current.length + 8) +
      ((13 * right.length + 18) + (13 * left.length + 18)) + 1)
      (data false v p f (record current ++ pending) leaves
        (record left ++ leftRest) (record right ++ rightRest))
      (data false false false true (record left ++ (record right ++ pending)) leaves leftRest rightRest) :=
    .ite_false rfl (.seq hs (.seq hb ha))
  convert h using 1
  omega

/-- Actual finite-program trace: emit the current record and preserve all suffixes. -/
theorem terminal_trace (bits rest leaves left right : List Bool) (v p f : Bool) :
    Trace program (13 * bits.length + 20)
      ((data true v p f (record bits ++ rest) leaves left right).withPC (some program.entry))
      ((data true false false f rest (record bits ++ leaves) left right).withPC none) := by
  have h := compiled_halt_trace (terminal_eval bits rest leaves left right v p f) 0 1
  simpa only [Nat.add_assoc] using h

/-- Actual finite-program trace: discard current, then push supplied B and A.
No read or copy of the accumulated pending or output suffix occurs. -/
theorem branch_trace (current left right pending leaves leftRest rightRest : List Bool)
    (v p f : Bool) :
    Trace program (5 * current.length + 13 * right.length + 13 * left.length + 46)
      ((data false v p f (record current ++ pending) leaves
        (record left ++ leftRest) (record right ++ rightRest)).withPC (some program.entry))
      ((data false false false true (record left ++ (record right ++ pending)) leaves
        leftRest rightRest).withPC none) := by
  have h := compiled_halt_trace (branch_eval current left right pending leaves leftRest rightRest v p f) 0 1
  simpa only [Nat.add_assoc] using h

/-- The bound depends only on the emitted record, never on old output length. -/
theorem terminal_cost_le (bits : List Bool) :
    13 * bits.length + 20 ≤ 10 * (record bits).length := by
  rw [record_length]
  omega

/-- Only the discarded record and the two child records enter the time bound. -/
theorem branch_cost_le (current left right : List Bool) :
    5 * current.length + 13 * right.length + 13 * left.length + 46 ≤
      10 * ((record current).length + (record left).length + (record right).length) := by
  simp only [record_length]
  omega

/-- The finite bit program has an actual primitive-machine execution with a
fixed linear factor. The old pending and leaf lengths are absent from the bound. -/
theorem terminal_primitive (bits rest leaves left right : List Bool) (v p f : Bool) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * (10 * (record bits).length))
      (BitProgram.primitiveCfg program
        ((data true v p f (record bits ++ rest) leaves left right).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((data true false false f rest (record bits ++ leaves) left right).withPC none)) :=
  (BitProgram.primitive_trace program (terminal_trace bits rest leaves left right v p f)).mono
    (Nat.mul_le_mul_left _ (terminal_cost_le bits))

theorem branch_primitive (current left right pending leaves leftRest rightRest : List Bool)
    (v p f : Bool) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program *
        (10 * ((record current).length + (record left).length + (record right).length)))
      (BitProgram.primitiveCfg program
        ((data false v p f (record current ++ pending) leaves
          (record left ++ leftRest) (record right ++ rightRest)).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((data false false false true (record left ++ (record right ++ pending)) leaves
          leftRest rightRest).withPC none)) :=
  (BitProgram.primitive_trace program
    (branch_trace current left right pending leaves leftRest rightRest v p f)).mono
    (Nat.mul_le_mul_left _ (branch_cost_le current left right))

/-- Instantiating a payload encoder connects the bit trace to a list worklist. -/
theorem terminal_list_trace {α : Type*} (enc : α → List Bool) (current : α)
    (pending leaves : List α) (pendingSuffix leavesSuffix left right : List Bool) (v p f : Bool) :
    Trace program (13 * (enc current).length + 20)
      ((data true v p f (Encoding.encodeList enc (current :: pending) ++ pendingSuffix)
        (Encoding.encodeList enc leaves ++ leavesSuffix) left right).withPC (some program.entry))
      ((data true false false f (Encoding.encodeList enc pending ++ pendingSuffix)
        (Encoding.encodeList enc (current :: leaves) ++ leavesSuffix) left right).withPC none) := by
  simpa only [Encoding.encodeList, record, List.cons_append, List.append_assoc] using
    terminal_trace (enc current) (Encoding.encodeList enc pending ++ pendingSuffix)
      (Encoding.encodeList enc leaves ++ leavesSuffix) left right v p f

theorem branch_list_trace {α : Type*} (enc : α → List Bool) (current left right : α)
    (pending : List α) (pendingSuffix leaves leftRest rightRest : List Bool) (v p f : Bool) :
    Trace program (5 * (enc current).length + 13 * (enc right).length + 13 * (enc left).length + 46)
      ((data false v p f (Encoding.encodeList enc (current :: pending) ++ pendingSuffix) leaves
        (record (enc left) ++ leftRest) (record (enc right) ++ rightRest)).withPC (some program.entry))
      ((data false false false true (Encoding.encodeList enc (left :: right :: pending) ++ pendingSuffix)
        leaves leftRest rightRest).withPC none) := by
  simpa only [Encoding.encodeList, record, List.cons_append, List.append_assoc] using
    branch_trace (enc current) (enc left) (enc right) (Encoding.encodeList enc pending ++ pendingSuffix)
      leaves leftRest rightRest v p f

end SubexponentialSAT.ExecWorklistProgram

end OAI.Algorithms
