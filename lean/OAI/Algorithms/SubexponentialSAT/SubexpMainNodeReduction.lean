import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutPorts
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram
import OAI.Algorithms.SubexponentialSAT.SubexpMainPreparedRings

namespace OAI.Algorithms

/-!
# Physically install the target reduction in the node workspace

The fixed three-stack program clears the old destination and temporary word,
copies the complete target reduction without consuming its persistent source,
and resets its sixteen registers. The Main embedding touches only persistent
14 and ordinary 91/319. The source/target ring banks and threshold tail are
therefore retained. The final cache theorem derives the copied word from the
actual prepared-ring result, rather than a supplied reduction word.
-/

namespace SubexponentialSAT.SubexpMainNodeReduction

open BitProgram StructuredCalls SubexpMainProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

namespace Local

open SubexpSetupStorage

abbrev Data := State 16 3
abbrev Code := Cmd 16 3

def prepared (a : Data) : Data := clearState 1 (clearState 2 a)
def copied (a : Data) : Data := copyState 0 1 (prepared a)
def result (a : Data) : Data := RegisterResetProgram.zeroed (copied a)

def command : Code := .seq (clearCmd 2)
  (.seq (clearCmd 1) (.seq (copyCmd 0 1 2) RegisterResetProgram.all))
abbrev program : Program 16 3 (size command + 1) := compiled command 0 1

def cost (a : Data) : ℕ :=
  7 * (a.stacks 0).length + 2 * (a.stacks 1).length + 2 * (a.stacks 2).length + 27

theorem prepared_temporary (a : Data) : (prepared a).stacks 2 = [] := by
  simp [prepared, clearState]

theorem command_eval (a : Data) : Eval command (cost a) a (result a) := by
  have hcopy := copy_eval (0 : Fin 3) 1 2 (prepared a)
    (by decide) (by decide) (by decide) (prepared_temporary a)
  have h := (clear_eval (2 : Fin 3) a).seq
    ((clear_eval (1 : Fin 3) (clearState 2 a)).seq
      (hcopy.seq (RegisterResetProgram.all_eval (copied a))))
  convert h using 1
  · rfl
  · simp [cost, prepared, clearState]
    omega
  · rfl

theorem result_target (a : Data) : (result a).stacks 1 = a.stacks 0 := by
  simp [result, copied, prepared, RegisterResetProgram.zeroed, copyState,
    clearState, StackRoutines.copyStacks]

theorem result_temporary (a : Data) : (result a).stacks 2 = [] := by
  simp [result, copied, prepared, RegisterResetProgram.zeroed, copyState,
    clearState, StackRoutines.copyStacks]

theorem result_frame (a : Data) (i : Fin 3) (h1 : i ≠ 1) (h2 : i ≠ 2) :
    (result a).stacks i = a.stacks i := by
  simp [result, copied, prepared, RegisterResetProgram.zeroed, copyState,
    clearState, StackRoutines.copyStacks, h1, h2]

theorem result_register (a : Data) (i : Fin 16) : (result a).regs i = false := rfl

end Local

def stackMap {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) :
    Fin 3 → Fin (totalStacks es) :=
  ![persistent es 14, SubexpLayoutPorts.ordinary alloc 91, SubexpLayoutPorts.ordinary alloc 319]

theorem stackMap_injective {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) :
    Function.Injective (stackMap alloc) := by
  intro i j hij
  have h := congrArg Fin.val hij
  have hw := alloc.enough.trans alloc.within
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals norm_num [stackMap, persistent, SubexpLayoutPorts.ordinary] at h <;> omega

def procedure (er : ℕ) {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) : Procedure er es where
  registers := 16
  stackCount := 3
  labels := size Local.command + 1
  program := Local.program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin (workRegs er) => k.val) h)⟩
  stack := ⟨stackMap alloc, stackMap_injective alloc⟩

def program (er : ℕ) {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) :=
  ProgramLinking.liftProgram (procedure er alloc).program
    (procedure er alloc).registerMap (procedure er alloc).stack

noncomputable def installed {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) : MainState er es :=
  (procedure er alloc).install a (Local.result ((procedure er alloc).project a))

theorem installed_target {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) :
    (installed alloc a).stacks (SubexpLayoutPorts.ordinary alloc 91) =
      a.stacks (persistent es 14) := by
  exact (embedState_stack (procedure er alloc).registerMap (procedure er alloc).stack
    a (Local.result ((procedure er alloc).project a)) (procedure er alloc).stack.injective
    (1 : Fin 3)).trans (Local.result_target ((procedure er alloc).project a))

theorem installed_temporary {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) :
    (installed alloc a).stacks (SubexpLayoutPorts.ordinary alloc 319) = [] := by
  exact (embedState_stack (procedure er alloc).registerMap (procedure er alloc).stack
    a (Local.result ((procedure er alloc).project a)) (procedure er alloc).stack.injective
    (2 : Fin 3)).trans (Local.result_temporary ((procedure er alloc).project a))

theorem installed_frame {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (j : Fin (totalStacks es))
    (h91 : j ≠ SubexpLayoutPorts.ordinary alloc 91)
    (h319 : j ≠ SubexpLayoutPorts.ordinary alloc 319) :
    (installed alloc a).stacks j = a.stacks j := by
  by_cases hm : ∃ i, stackMap alloc i = j
  · obtain ⟨i, rfl⟩ := hm
    have h1 : i ≠ 1 := by rintro rfl; exact h91 rfl
    have h2 : i ≠ 2 := by rintro rfl; exact h319 rfl
    exact (embedState_stack (procedure er alloc).registerMap (procedure er alloc).stack
      a (Local.result ((procedure er alloc).project a)) (procedure er alloc).stack.injective i).trans
        (Local.result_frame ((procedure er alloc).project a) i h1 h2)
  · exact embedState_stack_frame _ _ _ _ _ hm

theorem installed_persistent {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (i : Fin 32) :
    (installed alloc a).stacks (persistent es i) = a.stacks (persistent es i) := by
  apply installed_frame
  all_goals
    intro h
    have hv := congrArg Fin.val h
    have hw := alloc.enough.trans alloc.within
    norm_num [persistent, SubexpLayoutPorts.ordinary] at hv
    omega

theorem installed_threshold {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (j : Fin (totalStacks es)) (hj : alloc.ordinaryCount ≤ j.val) :
    (installed alloc a).stacks j = a.stacks j := by
  apply installed_frame
  all_goals
    intro h
    have hv := congrArg Fin.val h
    have hw := alloc.enough
    norm_num [SubexpLayoutPorts.ordinary] at hv
    omega

theorem installed_register {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (i : Fin 16) :
    (installed alloc a).regs ((procedure er alloc).registerMap i) = false := by
  exact (embedState_register (procedure er alloc).registerMap (procedure er alloc).stack
    a (Local.result ((procedure er alloc).project a)) (procedure er alloc).registerMap_injective i).trans
      (Local.result_register ((procedure er alloc).project a) i)

theorem installed_register_frame {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (i : Fin (totalRegs er)) (hi : 16 ≤ i.val) :
    (installed alloc a).regs i = a.regs i := by
  apply embedState_register_frame
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  have hlt : j.val < 16 := j.isLt
  omega

theorem installed_control {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (i : Fin 3) :
    (installed alloc a).regs (controlRegister er i) = a.regs (controlRegister er i) :=
  Procedure.install_control _ _ _ _

/-- Exact input-only invocation cost, including the compiled halt. Dirty
destination/temporary words are explicitly charged; unrelated data are not. -/
def runtimeBound {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) : ℕ :=
  7 * (a.stacks (persistent es 14)).length +
    2 * (a.stacks (SubexpLayoutPorts.ordinary alloc 91)).length +
    2 * (a.stacks (SubexpLayoutPorts.ordinary alloc 319)).length + 28

theorem invocation_cost {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) :
    Local.cost ((procedure er alloc).project a) + 1 = runtimeBound alloc a := by
  change 7 * (a.stacks (persistent es 14)).length +
    2 * (a.stacks (SubexpLayoutPorts.ordinary alloc 91)).length +
    2 * (a.stacks (SubexpLayoutPorts.ordinary alloc 319)).length + 27 + 1 = _
  unfold runtimeBound
  omega

theorem execution_exact {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) :
    Eval (procedure er alloc).invoke (runtimeBound alloc a) a (installed alloc a) := by
  have h := Procedure.invoke_trace (procedure er alloc) a
    (Local.result ((procedure er alloc).project a))
    (compiled_halt_trace (Local.command_eval ((procedure er alloc).project a)) 0 1)
  simpa only [invocation_cost, installed] using h

theorem execution {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) :
    ∃ n ≤ runtimeBound alloc a, Eval (procedure er alloc).invoke n a (installed alloc a) :=
  ⟨_, le_rfl, execution_exact alloc a⟩

theorem program_runsIn {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) :
    RunsIn (program er alloc) (runtimeBound alloc a)
      (a.withPC (some (program er alloc).entry)) ((installed alloc a).withPC none) := by
  have h := execution_exact alloc a
  change Eval (.call (program er alloc)) _ _ _ at h
  cases h with
  | call _ ht => exact ⟨_, le_rfl, ht⟩

theorem primitive_execution {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) :
    Computation.RunsIn (primitive (program er alloc)).step
      (primitiveOverhead (program er alloc) * runtimeBound alloc a)
      (primitiveCfg (program er alloc) (a.withPC (some (program er alloc).entry)))
      (primitiveCfg (program er alloc) ((installed alloc a).withPC none)) :=
  BitProgram.primitive_execution _ (program_runsIn alloc a)

/-- The destination is the actual target prepared ring's complete reduction
quartet, obtained from the previously executed two-bank staging contract. -/
theorem installed_from_prepared {er es : ℕ}
    (alloc : SubexpLayoutPorts.Allocation es) (ringAlloc : SubexpMainPreparedRings.Allocation es)
    (before a : MainState er es) (p D : ℕ) [Fact p.Prime]
    (coeff : SubexpQuarticRing.Quad (SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) =
      SubexpQuarticRing.Quad.ofFn (QuarticSearch.coefficients p))
    (hprepared : SubexpMainPreparedRings.Result ringAlloc before a p D coeff hc) :
    (installed alloc a).stacks (SubexpLayoutPorts.ordinary alloc 91) =
      SubexpPreparedQuarticSetup.flat (SubexpPreparedQuarticSetup.preparedData p D coeff hc).reduction := by
  exact (installed_target alloc a).trans (hprepared.target (2 : Fin 6))

end SubexponentialSAT.SubexpMainNodeReduction

end OAI.Algorithms
