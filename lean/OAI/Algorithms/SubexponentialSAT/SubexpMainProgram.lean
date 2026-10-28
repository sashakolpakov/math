import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpFrontendPrefix
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-!
# Fixed top-level SAT controller and caller storage convention

The controller hardwires the checked raw-input frontend, concrete framed-record
iteration, physical payload transfer, and output-bit handling. Remaining phases
are supplied as actual finite BitPrograms with explicit injective port maps.
Their semantic and resource contracts remain separate proof obligations.

The workspace has at least 16 Boolean registers and 128 stacks, plus fixed
extra space chosen with the clause width. Three further registers belong to the
record iterator. Thirty-two persistent stacks are disjoint from the workspace:
0..5 retain the raw-frontend ABI; 6 prime; 7 leaf stream; 8 reversed parser payload;
9 forward current leaf; 10 leaf answer; 11 final output; 12 modulus; 13 cell width;
14/15 field/basis data; 16 delta; 17 Q; 18 block size; 19 dimension; 20 threshold;
21 colors; 22 lifting precision. Later slots are explicit spare persistent data.
-/

namespace SubexponentialSAT.SubexpMainProgram

open StructuredCalls

def workRegs (extra : ℕ) : ℕ := 16 + extra
def workStacks (extra : ℕ) : ℕ := 128 + extra
def totalRegs (extra : ℕ) : ℕ := workRegs extra + 3
def totalStacks (extra : ℕ) : ℕ := workStacks extra + 32

abbrev MainState (er es : ℕ) := StructuredProgram.State (totalRegs er) (totalStacks es)
abbrev MainCmd (er es : ℕ) := StructuredCalls.Cmd (totalRegs er) (totalStacks es)

def workRegister (er : ℕ) (i : Fin (workRegs er)) : Fin (totalRegs er) := i.castAdd 3
def controlRegister (er : ℕ) (i : Fin 3) : Fin (totalRegs er) := i.natAdd (workRegs er)
def persistent (es : ℕ) (i : Fin 32) : Fin (totalStacks es) := i.natAdd (workStacks es)

def scratchValue (er : ℕ) : Fin (totalRegs er) := workRegister er ⟨0, by simp [workRegs]⟩
def scratchPresent (er : ℕ) : Fin (totalRegs er) := workRegister er ⟨1, by dsimp [workRegs]; omega⟩

theorem workRegister_injective (er : ℕ) : Function.Injective (workRegister er) := by
  intro a b h
  have hv := congrArg Fin.val h
  exact Fin.ext hv

theorem controlRegister_injective (er : ℕ) : Function.Injective (controlRegister er) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa [controlRegister] using hv

theorem persistent_injective (es : ℕ) : Function.Injective (persistent es) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa [persistent] using hv

theorem work_ne_control (er : ℕ) (i : Fin (workRegs er)) (j : Fin 3) :
    workRegister er i ≠ controlRegister er j := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = workRegs er + j.val at hv
  omega

def ports (er es : ℕ) : RecordPrograms.Ports (totalRegs er) (totalStacks es) where
  tag := controlRegister er 0
  present := controlRegister er 1
  found := controlRegister er 2
  source := persistent es 7
  payload := persistent es 8
  tag_ne_present := fun h => by have := (controlRegister_injective er) h; contradiction
  found_ne_tag := fun h => by have := (controlRegister_injective er) h; contradiction
  found_ne_present := fun h => by have := (controlRegister_injective er) h; contradiction
  source_ne_payload := fun h => by have := (persistent_injective es) h; contradiction

/-- A supplied phase is a fixed finite instruction table with explicit port
allocation. Its register map cannot touch any iterator-control bit. -/
structure Procedure (er es : ℕ) where
  registers : ℕ
  stackCount : ℕ
  labels : ℕ
  program : BitProgram.Program registers stackCount labels
  register : Fin registers ↪ Fin (workRegs er)
  stack : Fin stackCount ↪ Fin (totalStacks es)

namespace Procedure

variable {er es : ℕ}

def registerMap (p : Procedure er es) : Fin p.registers → Fin (totalRegs er) :=
  workRegister er ∘ p.register

theorem registerMap_injective (p : Procedure er es) : Function.Injective p.registerMap :=
  (workRegister_injective er).comp p.register.injective

def invoke (p : Procedure er es) : MainCmd er es :=
  .call (ProgramLinking.liftProgram p.program p.registerMap p.stack)

def project (p : Procedure er es) (a : MainState er es) : StructuredProgram.State p.registers p.stackCount :=
  ⟨a.regs ∘ p.registerMap, a.stacks ∘ p.stack⟩

noncomputable def install (p : Procedure er es) (a : MainState er es)
    (result : StructuredProgram.State p.registers p.stackCount) : MainState er es :=
  embedState p.registerMap p.stack a result

private theorem extend_restrict {α β γ : Type} (f : α → β) (hf : Function.Injective f)
    (g : β → γ) : Function.extend f (g ∘ f) g = g := by
  funext i
  by_cases hi : ∃ j, f j = i
  · obtain ⟨j, rfl⟩ := hi
    exact hf.extend_apply _ _ _
  · exact Function.extend_apply' _ _ _ hi

@[simp] theorem install_project (p : Procedure er es) (a : MainState er es) :
    p.install a (p.project a) = a := by
  unfold install embedState project
  simp only [extend_restrict p.registerMap p.registerMap_injective,
    extend_restrict p.stack p.stack.injective]

theorem invoke_trace (p : Procedure er es) (a : MainState er es)
    (result : StructuredProgram.State p.registers p.stackCount) {n : ℕ}
    (h : BitProgram.Trace p.program n
      ((p.project a).withPC (some p.program.entry)) (result.withPC none)) :
    Eval p.invoke n a (p.install a result) := by
  have he := eval_call_lifted p.program p.registerMap p.stack a
    p.registerMap_injective p.stack.injective h
  change Eval p.invoke n (p.install a (p.project a)) (p.install a result) at he
  simpa only [install_project] using he

theorem install_control (p : Procedure er es) (a : MainState er es)
    (result : StructuredProgram.State p.registers p.stackCount) (j : Fin 3) :
    (p.install a result).regs (controlRegister er j) = a.regs (controlRegister er j) := by
  apply embedState_register_frame
  rintro ⟨i, hi⟩
  exact work_ne_control er (p.register i) j hi

end Procedure

/-- The real published parser/parameter frontend, allocated to persistent ports
0..5. No abstract preprocessing callback replaces it. -/
def frontendProcedure (er es : ℕ) : Procedure er es where
  registers := 3
  stackCount := 6
  labels := StructuredCalls.size SubexpFrontendPrefix.command + 1
  program := SubexpFrontendPrefix.program
  register :=
    ⟨fun i => i.castLE (by simp [workRegs]; omega), by
      intro a b h
      have hv := congrArg Fin.val h
      exact Fin.ext hv⟩
  stack :=
    ⟨fun i => persistent es (i.castAdd 26), by
      intro a b h
      have hv := congrArg Fin.val ((persistent_injective es) h)
      exact Fin.ext hv⟩

def initialData (er es : ℕ) (input : List Bool) : MainState er es :=
  StructuredProgram.ioState (persistent es 0) input

theorem prefix_project_initial (er es : ℕ) (input : List Bool) :
    (frontendProcedure er es).project (initialData er es input) =
      @StructuredProgram.ioState 3 6 0 input := by
  unfold Procedure.project initialData StructuredProgram.ioState
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    change Fin 6 at i
    change (if persistent es (i.castAdd 26) = persistent es 0 then input else []) =
      (if i = 0 then input else [])
    have hi : i.castAdd 26 = (0 : Fin 32) ↔ i = 0 := by
      constructor
      · intro h
        have hv := congrArg Fin.val h
        exact Fin.ext hv
      · rintro rfl
        rfl
    simp only [(persistent_injective es).eq_iff, hi]

noncomputable def prefixData (er es : ℕ) (input body nb sb ub : List Bool) : MainState er es :=
  (frontendProcedure er es).install (initialData er es input) (SubexpFrontendPrefix.state body nb sb ub)

/-- The first real phase accepts the existing canonical raw CNF syntax. -/
theorem prefix_execution (er es : ℕ) {n : ℕ} (F : SAT.CNF (Fin n)) :
    ∃ (nb sb ub : List Bool) (steps : ℕ),
      CounterPrograms.value nb = n ∧
      CounterPrograms.value sb = SubexpPackingParameters.s n ∧
      CounterPrograms.value ub = SubexpPackingParameters.u n ∧
      steps ≤ SubexpFrontendPrefix.bound (Encoding.formulaBitLength F) ∧
      Eval (frontendProcedure er es).invoke steps (initialData er es (Encoding.encodeCNF F))
        (prefixData er es (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) nb sb ub) := by
  obtain ⟨nb, sb, ub, hn, hs, hu, _, _, _, steps, hsteps, ht⟩ :=
    SubexpFrontendPrefix.run_formula F
  refine ⟨nb, sb, ub, steps, hn, hs, hu, hsteps, ?_⟩
  apply Procedure.invoke_trace
  rw [prefix_project_initial]
  change BitProgram.Trace SubexpFrontendPrefix.program steps
    (BitProgram.initial SubexpFrontendPrefix.program (Encoding.encodeCNF F))
    ((SubexpFrontendPrefix.state (Encoding.encodeCNFBody F) nb sb ub).withPC none)
  exact ht

/-- The fields must be instantiated by real fixed finite programs. The record
contains no semantic function, answer, running-time annotation, or oracle. -/
structure Phases (er es : ℕ) where
  setup : Procedure er es
  sparsify : Procedure er es
  layout : Procedure er es
  moments : Procedure er es
  crt : Procedure er es
  decode : Procedure er es

def atom {er es : ℕ} (a : StructuredProgram.Atom (totalRegs er) (totalStacks es)) : MainCmd er es :=
  .base (.atom a)

def transferLeaf (er es : ℕ) : MainCmd er es :=
  .call (StackRoutines.transferProgram (persistent es 8) (persistent es 9)
    (scratchValue er) (scratchPresent er))

def clearPort (er es : ℕ) (p : Fin (totalStacks es)) : MainCmd er es :=
  .call (StackRoutines.clearProgram p (scratchValue er) (scratchPresent er))

def finishLeaf (er es : ℕ) : MainCmd er es :=
  .seq (atom (.pop (persistent es 10) (controlRegister er 2) (controlRegister er 1)))
    (.seq (clearPort er es (persistent es 9))
      (.seq (clearPort er es (persistent es 10))
        (.seq (atom (.set (controlRegister er 0) false))
          (atom (.set (controlRegister er 1) true)))))

def leafCallback {er es : ℕ} (p : Phases er es) : MainCmd er es :=
  .seq (transferLeaf er es)
    (.seq p.layout.invoke (.seq p.moments.invoke (.seq p.crt.invoke
      (.seq p.decode.invoke (finishLeaf er es)))))

def emitAnswer (er es : ℕ) : MainCmd er es :=
  atom (.push (persistent es 11) (controlRegister er 2))

/-- One concrete control graph: raw frontend, setup, actual sparsifier call,
framed leaf traversal with early success, and a physical output-bit push. -/
def command {er es : ℕ} (p : Phases er es) : MainCmd er es :=
  .seq (frontendProcedure er es).invoke (.seq p.setup.invoke (.seq p.sparsify.invoke
    (.seq (RecordPrograms.iterate (ports er es) (leafCallback p)) (emitAnswer er es))))

def program {er es : ℕ} (p : Phases er es) :=
  StructuredCalls.compiled (command p) (persistent es 0) (persistent es 11)

end SubexponentialSAT.SubexpMainProgram
namespace SubexponentialSAT.SubexpMainProgram

open StructuredCalls

variable {er es : ℕ}

@[simp] theorem control_eq_iff (er : ℕ) (i j : Fin 3) :
    controlRegister er i = controlRegister er j ↔ i = j :=
  (controlRegister_injective er).eq_iff

@[simp] theorem persistent_eq_iff (es : ℕ) (i j : Fin 32) :
    persistent es i = persistent es j ↔ i = j := (persistent_injective es).eq_iff

@[simp] theorem control_ne_scratchValue (er : ℕ) (i : Fin 3) :
    controlRegister er i ≠ scratchValue er := (work_ne_control er _ i).symm

@[simp] theorem control_ne_scratchPresent (er : ℕ) (i : Fin 3) :
    controlRegister er i ≠ scratchPresent er := (work_ne_control er _ i).symm

theorem scratch_ne (er : ℕ) : scratchValue er ≠ scratchPresent er := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [scratchValue, scratchPresent, workRegister] at hv

def transferredData (a : MainState er es) : MainState er es :=
  ⟨BitProgram.readRegs a.regs (scratchValue er) (scratchPresent er) none,
    StackRoutines.transferStacks (persistent es 8) (persistent es 9) a.stacks⟩

def transferCost (a : MainState er es) : ℕ := 3 * (a.stacks (persistent es 8)).length + 3

/-- A real transfer reverses the parser's reversed payload into the current
leaf stack and empties the parser payload. -/
theorem transferLeaf_eval (a : MainState er es) :
    Eval (transferLeaf er es) (transferCost a) a (transferredData a) := by
  have h := StackRoutines.transferProgram_trace (persistent es 8) (persistent es 9)
    (scratchValue er) (scratchPresent er) (by simp) (scratch_ne er) a.regs a.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  apply Eval.call
  simpa [transferCost, transferredData, StructuredProgram.State.withPC,
    StackRoutines.transferResult, StackRoutines.transferProgram,
    Nat.add_assoc] using hh

@[simp] theorem transferred_payload (a : MainState er es) :
    (transferredData a).stacks (persistent es 8) = [] := by
  simp [transferredData, StackRoutines.transferStacks]

@[simp] theorem transferred_leaf (a : MainState er es) :
    (transferredData a).stacks (persistent es 9) =
      (a.stacks (persistent es 8)).reverse ++ a.stacks (persistent es 9) := by
  simp [transferredData]

@[simp] theorem transferred_source (a : MainState er es) :
    (transferredData a).stacks (persistent es 7) = a.stacks (persistent es 7) := by
  simp [transferredData, StackRoutines.transferStacks]

def clearedData (p : Fin (totalStacks es)) (a : MainState er es) : MainState er es :=
  ⟨BitProgram.readRegs a.regs (scratchValue er) (scratchPresent er) none,
    StackRoutines.clearStacks p a.stacks⟩

def clearCost (p : Fin (totalStacks es)) (a : MainState er es) : ℕ :=
  2 * (a.stacks p).length + 3

theorem clearPort_eval (p : Fin (totalStacks es)) (a : MainState er es) :
    Eval (clearPort er es p) (clearCost p a) a (clearedData p a) := by
  have h := StackRoutines.clearProgram_trace p (scratchValue er) (scratchPresent er) a.regs a.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  apply Eval.call
  simpa [clearCost, clearedData, StructuredProgram.State.withPC,
    StackRoutines.clearResult, StackRoutines.clearProgram,
    Nat.add_assoc] using hh

def poppedAnswer (a : MainState er es) : MainState er es :=
  StructuredProgram.Atom.eval (.pop (persistent es 10) (controlRegister er 2) (controlRegister er 1)) a

def finishedData (a : MainState er es) : MainState er es :=
  StructuredProgram.Atom.eval (.set (controlRegister er 1) true)
    (StructuredProgram.Atom.eval (.set (controlRegister er 0) false)
      (clearedData (persistent es 10) (clearedData (persistent es 9) (poppedAnswer a))))

def finishCost (a : MainState er es) : ℕ :=
  1 + (clearCost (persistent es 9) (poppedAnswer a) +
    (clearCost (persistent es 10) (clearedData (persistent es 9) (poppedAnswer a)) + (1 + 1)))

/-- Pop the real decoded answer, clear reusable leaf storage with real loops,
and restore the record reader's control bits. -/
theorem finishLeaf_eval (a : MainState er es) :
    Eval (finishLeaf er es) (finishCost a) a (finishedData a) :=
  .seq (.base (.atom _ a))
    (.seq (clearPort_eval _ _)
      (.seq (clearPort_eval _ _) (.seq (.base (.atom _ _)) (.base (.atom _ _)))))

@[simp] theorem finished_tag (a : MainState er es) :
    (finishedData a).regs (controlRegister er 0) = false := by
  simp [finishedData, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, BitProgram.execInstr]

@[simp] theorem finished_present (a : MainState er es) :
    (finishedData a).regs (controlRegister er 1) = true := by
  simp [finishedData, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, BitProgram.execInstr]

@[simp] theorem finished_found (a : MainState er es) :
    (finishedData a).regs (controlRegister er 2) =
      (a.stacks (persistent es 10)).head?.getD false := by
  simp [finishedData, poppedAnswer, clearedData, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, BitProgram.execInstr, BitProgram.readRegs]

@[simp] theorem finished_source (a : MainState er es) :
    (finishedData a).stacks (persistent es 7) = a.stacks (persistent es 7) := by
  simp [finishedData, poppedAnswer, clearedData, StackRoutines.clearStacks,
    StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, BitProgram.execInstr]

@[simp] theorem finished_payload (a : MainState er es) :
    (finishedData a).stacks (persistent es 8) = a.stacks (persistent es 8) := by
  simp [finishedData, poppedAnswer, clearedData, StackRoutines.clearStacks,
    StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, BitProgram.execInstr]

@[simp] theorem finished_leaf (a : MainState er es) :
    (finishedData a).stacks (persistent es 9) = [] := by
  simp [finishedData, poppedAnswer, clearedData, StackRoutines.clearStacks,
    StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, BitProgram.execInstr]

@[simp] theorem finished_answer (a : MainState er es) :
    (finishedData a).stacks (persistent es 10) = [] := by
  simp [finishedData, poppedAnswer, clearedData, StackRoutines.clearStacks,
    StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, BitProgram.execInstr]

theorem finished_record_state (a : MainState er es) (tail : List Bool) (answer : Bool)
    (hs : a.stacks (persistent es 7) = tail) (hp : a.stacks (persistent es 8) = [])
    (ha : (a.stacks (persistent es 10)).head? = some answer) :
    finishedData a = RecordPrograms.state (ports er es) (finishedData a) false true answer tail [] := by
  symm
  apply RecordPrograms.state_eq_self
  · exact finished_tag a
  · exact finished_present a
  · simp [ports, ha]
  · simp [ports, hs]
  · simp [ports, hp]

def emittedData (a : MainState er es) : MainState er es :=
  StructuredProgram.Atom.eval (.push (persistent es 11) (controlRegister er 2)) a

theorem emitAnswer_eval (a : MainState er es) :
    Eval (emitAnswer er es) 1 a (emittedData a) := .base (.atom _ _)

@[simp] theorem emitted_head (a : MainState er es) :
    ((emittedData a).stacks (persistent es 11)).head? = some (a.regs (controlRegister er 2)) := by
  simp [emittedData, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, BitProgram.execInstr]

end SubexponentialSAT.SubexpMainProgram
namespace SubexponentialSAT.SubexpMainProgram

open StructuredCalls

variable {er es : ℕ}

/-- Concrete executions of the four fixed leaf-processing programs. The
successive states and instruction counts are witnesses, not runtime inputs. -/
structure LeafRun (p : Phases er es) (start : MainState er es) where
  afterLayout : MainState er es
  afterMoments : MainState er es
  afterCRT : MainState er es
  afterDecode : MainState er es
  layoutSteps : ℕ
  momentSteps : ℕ
  crtSteps : ℕ
  decodeSteps : ℕ
  layoutTrace : Eval p.layout.invoke layoutSteps (transferredData start) afterLayout
  momentTrace : Eval p.moments.invoke momentSteps afterLayout afterMoments
  crtTrace : Eval p.crt.invoke crtSteps afterMoments afterCRT
  decodeTrace : Eval p.decode.invoke decodeSteps afterCRT afterDecode

namespace LeafRun

def steps {p : Phases er es} {start : MainState er es} (run : LeafRun p start) : ℕ :=
  transferCost start + (run.layoutSteps + (run.momentSteps +
    (run.crtSteps + (run.decodeSteps + finishCost run.afterDecode))))

theorem execution {p : Phases er es} {start : MainState er es} (run : LeafRun p start) :
    Eval (leafCallback p) run.steps start (finishedData run.afterDecode) :=
  .seq (transferLeaf_eval start) (.seq run.layoutTrace (.seq run.momentTrace
    (.seq run.crtTrace (.seq run.decodeTrace (finishLeaf_eval run.afterDecode)))))

end LeafRun

/-- This is the physical state passed to a leaf callback by the framed parser. -/
def leafInput (base : MainState er es) (tail bits : List Bool) : MainState er es :=
  RecordPrograms.state (ports er es) base false true false tail bits.reverse

theorem transfer_leafInput (base : MainState er es) (tail bits : List Bool)
    (empty : base.stacks (persistent es 9) = []) :
    (transferredData (leafInput base tail bits)).stacks (persistent es 9) = bits ∧
    (transferredData (leafInput base tail bits)).stacks (persistent es 8) = [] ∧
    (transferredData (leafInput base tail bits)).stacks (persistent es 7) = tail := by
  simp [leafInput, RecordPrograms.state, ports, empty]

/-- Every permitted leaf has measured executions of the actual four phase
programs. In addition to the computed answer, the contract explicitly restores
the pending record stream and parser payload. No Boolean test is executed by
this proposition: the program obtains its answer from its real decoder stack. -/
def LeafContract (p : Phases er es) (test : List Bool → Bool)
    (cost : List Bool → ℕ) (invariant : MainState er es → Prop)
    (validPayload : List Bool → Prop) : Prop :=
  ∀ (bits tail : List Bool) (base : MainState er es), validPayload bits → invariant base →
    ∃ run : LeafRun p (leafInput base tail bits),
      run.steps ≤ cost bits ∧ invariant (finishedData run.afterDecode) ∧
      run.afterDecode.stacks (persistent es 7) = tail ∧
      run.afterDecode.stacks (persistent es 8) = [] ∧
      (run.afterDecode.stacks (persistent es 10)).head? = some (test bits)

theorem callback_contract {p : Phases er es} {test : List Bool → Bool}
    {cost : List Bool → ℕ} {invariant : MainState er es → Prop}
    {validPayload : List Bool → Prop}
    (contract : LeafContract p test cost invariant validPayload) :
    RecordPrograms.CallbackContractOn (ports er es) (leafCallback p)
      test cost invariant validPayload := by
  intro bits tail base hv hi
  obtain ⟨run, hn, hinv, hs, hp, ha⟩ := contract bits tail base hv hi
  refine ⟨run.steps, finishedData run.afterDecode, hn, hinv, ?_⟩
  have he := run.execution
  rw [finished_record_state run.afterDecode tail (test bits) hs hp ha] at he
  exact he

/-- The fixed setup and sparsification procedures execute before leaf traversal.
The final state contains actual encoded leaf records produced by the latter. -/
structure BootRun (p : Phases er es) (afterPrefix : MainState er es) where
  afterSetup : MainState er es
  afterSparsify : MainState er es
  setupSteps : ℕ
  sparsifySteps : ℕ
  setupTrace : Eval p.setup.invoke setupSteps afterPrefix afterSetup
  sparsifyTrace : Eval p.sparsify.invoke sparsifySteps afterSetup afterSparsify

/-- All costs are real source instruction counts. The iterator pays for each
frame parse, leaf transfer, four phase calls, cleanup, branch, and final push.
The final state may retain workspace and persistent scalar data. -/
theorem command_execution {p : Phases er es} {input : List Bool}
    {afterPrefix : MainState er es} {prefixSteps : ℕ}
    (prefixTrace : Eval (frontendProcedure er es).invoke prefixSteps
      (initialData er es input) afterPrefix)
    (boot : BootRun p afterPrefix)
    (records : List (List Bool)) (test : List Bool → Bool) (cost : List Bool → ℕ)
    (invariant : MainState er es → Prop) (validPayload : List Bool → Prop)
    (contract : LeafContract p test cost invariant validPayload)
    (validRecords : ∀ bits ∈ records, validPayload bits)
    (valid : invariant boot.afterSparsify)
    (source : boot.afterSparsify.stacks (persistent es 7) = Encoding.encodeList id records)
    (payload : boot.afterSparsify.stacks (persistent es 8) = []) :
    ∃ (n : ℕ) (final : MainState er es),
      n ≤ prefixSteps + boot.setupSteps + boot.sparsifySteps +
        4 + RecordPrograms.budget cost records ∧
      Eval (command p) n (initialData er es input) final ∧
      (final.stacks (persistent es 11)).head? = some (records.any test) := by
  let a := boot.afterSparsify
  have ha : RecordPrograms.state (ports er es) a
      (a.regs (controlRegister er 0)) (a.regs (controlRegister er 1))
      (a.regs (controlRegister er 2)) (Encoding.encodeList id records ++ []) [] = a := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa [a, ports] using source
    · exact payload
  obtain ⟨n, next, hn, _, hi⟩ := RecordPrograms.iterate_run_on
    (ports er es) (leafCallback p) test cost invariant validPayload
    (callback_contract contract) records [] a validRecords valid
    (a.regs (controlRegister er 0)) (a.regs (controlRegister er 1))
    (a.regs (controlRegister er 2))
  rw [ha] at hi
  let last := RecordPrograms.state (ports er es) next false true (records.any test)
    (RecordPrograms.unread test records []) []
  refine ⟨prefixSteps + (boot.setupSteps + (boot.sparsifySteps + (n + 1))),
    emittedData last, by omega, ?_, ?_⟩
  · exact .seq prefixTrace (.seq boot.setupTrace (.seq boot.sparsifyTrace
      (.seq hi (emitAnswer_eval last))))
  · rw [emitted_head]
    exact congrArg some (RecordPrograms.state_found (ports er es) next false true
      (records.any test) (RecordPrograms.unread test records []) [])

/-- Source-code compilation has one final halt and no uncharged semantic step. -/
theorem compiled_execution {p : Phases er es} {input : List Bool}
    {n : ℕ} {final : MainState er es}
    (h : Eval (command p) n (initialData er es input) final) :
    BitProgram.Trace (program p) (n + 1) (BitProgram.initial (program p) input)
      (final.withPC none) :=
  StructuredCalls.compiled_halt_trace h (persistent es 0) (persistent es 11)

/-- The actual primitive binary-tape machine returns the head bit while allowing
all other final work data to remain. Its overhead is fixed by the finite code. -/
theorem primitive_execution {p : Phases er es} {input : List Bool}
    {n : ℕ} {final : MainState er es} {answer : Bool}
    (h : Eval (command p) n (initialData er es input) final)
    (output : (final.stacks (persistent es 11)).head? = some answer) :
    (BitProgram.primitive (program p)).OutputsInTime input answer
      (BitProgram.primitiveOverhead (program p) * (n + 1)) := by
  apply BitProgram.primitive_outputs_of_halted (program p)
    ⟨n + 1, le_rfl, compiled_execution h⟩ rfl
  exact output

end SubexponentialSAT.SubexpMainProgram

end OAI.Algorithms
