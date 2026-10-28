import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainScalarAlphabet
import OAI.Algorithms.SubexponentialSAT.SubexpDenseProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisEntry
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-! Actual unary frame-width metadata for the Main scalar cache. -/

namespace SubexponentialSAT.SubexpMainScalarFrameWidth

open BitProgram StructuredCalls SubexpMainProgram
open Subexp

abbrev Data := State 3 3
abbrev Code := Cmd 3 3

def clear (port : Fin 3) : Code := .call (StackRoutines.clearProgram port 0 1)
def afterClear (a : Data) (port : Fin 3) : Data :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks port []⟩
def prepared (a : Data) : Data := afterClear (afterClear a 1) 2
def counted (a : Data) : Data :=
  ⟨![false, false, true], ![a.stacks 0, List.replicate (a.stacks 0).length true, []]⟩
def result (a : Data) : Data := RegisterResetProgram.zeroed (counted a)

def command : Code := .seq (clear 1) (.seq (clear 2)
  (.seq (.call SubexpDenseProgram.KeyWidth.program) RegisterResetProgram.all))
abbrev program : Program 3 3 (size command + 1) := compiled command 0 1

def cost (a : Data) : ℕ :=
  7 * (a.stacks 0).length + 2 * (a.stacks 1).length + 2 * (a.stacks 2).length + 15

theorem clear_eval (a : Data) (port : Fin 3) :
    Eval (clear port) (2 * (a.stacks port).length + 3) a (afterClear a port) :=
  .call _ (ListRegisterProgram.clear_run port (0 : Fin 3) 1 a.regs a.stacks)

theorem prepared_stacks (a : Data) : (prepared a).stacks = ![a.stacks 0, [], []] := by
  funext i
  fin_cases i <;> simp [prepared, afterClear]

theorem count_eval (a : Data) :
    Eval (.call SubexpDenseProgram.KeyWidth.program) (7 * (a.stacks 0).length + 6)
      (prepared a) (counted a) := by
  have hr : ![(prepared a).regs 0, (prepared a).regs 1, (prepared a).regs 2] =
      (prepared a).regs := by
    funext i
    fin_cases i <;> rfl
  have ht := SubexpDenseProgram.KeyWidth.program_trace (a.stacks 0) []
    ((prepared a).regs 0) ((prepared a).regs 1) ((prepared a).regs 2)
  apply Eval.call
  simpa only [SubexpDenseProgram.KeyWidth.cfg, List.append_nil, hr,
    StructuredProgram.State.withPC, prepared_stacks, counted] using ht

theorem command_eval (a : Data) : Eval command (cost a) a (result a) := by
  have h := (clear_eval a 1).seq ((clear_eval (afterClear a 1) 2).seq
    ((count_eval a).seq (RegisterResetProgram.all_eval (counted a))))
  convert h using 1
  · rfl
  · have hstack : ((afterClear a 1).stacks 2).length = (a.stacks 2).length := by
      simp [afterClear]
    rw [hstack]
    unfold cost
    omega
  · rfl

theorem program_trace (a : Data) : Trace program (cost a + 1)
    (a.withPC (some program.entry)) ((result a).withPC none) :=
  compiled_halt_trace (command_eval a) 0 1

def sourcePort {es : ℕ} (a : SubexpLayoutPorts.Allocation es) := SubexpLayoutPorts.master a 26
def widthPort {es : ℕ} (a : SubexpLayoutPorts.Allocation es) := SubexpLayoutPorts.master a 20
def workPort {es : ℕ} (a : SubexpLayoutPorts.Allocation es) := SubexpLayoutPorts.ordinary a 319
def stackMap {es : ℕ} (a : SubexpLayoutPorts.Allocation es) : Fin 3 → Fin (totalStacks es) :=
  ![sourcePort a, widthPort a, workPort a]

theorem stackMap_value {es : ℕ} (a : SubexpLayoutPorts.Allocation es) (i : Fin 3) :
    (stackMap a i).val = (![666, 660, 319] : Fin 3 → ℕ) i := by
  fin_cases i <;> rfl

theorem stackMap_injective {es : ℕ} (a : SubexpLayoutPorts.Allocation es) :
    Function.Injective (stackMap a) := by
  have hvalues : Function.Injective (![666, 660, 319] : Fin 3 → ℕ) := by decide
  intro i j hij
  apply hvalues
  rw [← stackMap_value a i, ← stackMap_value a j]
  exact congrArg (fun k : Fin (totalStacks es) => k.val) hij

def procedure (er : ℕ) {es : ℕ} (a : SubexpLayoutPorts.Allocation es) : Procedure er es where
  registers := 3
  stackCount := 3
  labels := size command + 1
  program := program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j hij
    exact Fin.ext (congrArg (fun k : Fin (workRegs er) => k.val) hij)⟩
  stack := ⟨stackMap a, stackMap_injective a⟩

noncomputable def installed {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) : MainState er es :=
  (procedure er alloc).install a (result ((procedure er alloc).project a))

theorem installed_width {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) :
    (installed alloc a).stacks (widthPort alloc) =
      List.replicate (a.stacks (sourcePort alloc)).length true :=
  embedState_stack (procedure er alloc).registerMap (procedure er alloc).stack a
    (result ((procedure er alloc).project a)) (procedure er alloc).stack.injective (1 : Fin 3)

theorem installed_source {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) :
    (installed alloc a).stacks (sourcePort alloc) = a.stacks (sourcePort alloc) :=
  embedState_stack (procedure er alloc).registerMap (procedure er alloc).stack a
    (result ((procedure er alloc).project a)) (procedure er alloc).stack.injective (0 : Fin 3)

theorem installed_work {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) : (installed alloc a).stacks (workPort alloc) = [] :=
  embedState_stack (procedure er alloc).registerMap (procedure er alloc).stack a
    (result ((procedure er alloc).project a)) (procedure er alloc).stack.injective (2 : Fin 3)

theorem installed_frame {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (j : Fin (totalStacks es))
    (hw : widthPort alloc ≠ j) (ht : workPort alloc ≠ j) :
    (installed alloc a).stacks j = a.stacks j := by
  by_cases hm : ∃ i, stackMap alloc i = j
  · obtain ⟨i, rfl⟩ := hm
    fin_cases i
    · exact installed_source alloc a
    · exact False.elim (hw rfl)
    · exact False.elim (ht rfl)
  · exact embedState_stack_frame (procedure er alloc).registerMap (procedure er alloc).stack
      a (result ((procedure er alloc).project a)) j hm

theorem installed_control {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (i : Fin 3) :
    (installed alloc a).regs (controlRegister er i) = a.regs (controlRegister er i) :=
  Procedure.install_control _ _ _ _

theorem installed_register {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (i : Fin 3) :
    (installed alloc a).regs ((procedure er alloc).registerMap i) = false :=
  embedState_register (procedure er alloc).registerMap (procedure er alloc).stack a
    (result ((procedure er alloc).project a)) (procedure er alloc).registerMap_injective i

def runtimeBound {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) (a : MainState er es) : ℕ :=
  7 * (a.stacks (sourcePort alloc)).length + 2 * (a.stacks (widthPort alloc)).length +
    2 * (a.stacks (workPort alloc)).length + 16

theorem execution {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) (a : MainState er es) :
    Eval (procedure er alloc).invoke (runtimeBound alloc a) a (installed alloc a) := by
  have h := Procedure.invoke_trace (procedure er alloc) a _ (program_trace ((procedure er alloc).project a))
  exact h

theorem installed_scalar_width {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (p : ℕ)
    (hsource : a.stacks (sourcePort alloc) = Encoding.frame (MatrixWordEncoding.word p 0)) :
    (installed alloc a).stacks (widthPort alloc) = List.replicate (GlobalBasisEntry.frameWidth p) true := by
  rw [installed_width, hsource]
  simp [GlobalBasisEntry.frameWidth]

theorem after_scalar_alphabet {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] :
    (installed alloc (SubexpMainScalarAlphabet.installed alloc a p)).stacks (widthPort alloc) =
      List.replicate (GlobalBasisEntry.frameWidth p) true := by
  apply installed_scalar_width
  exact SubexpMainScalarAlphabet.installed_target alloc a p (5 : Fin 7)

end SubexponentialSAT.SubexpMainScalarFrameWidth

end OAI.Algorithms
