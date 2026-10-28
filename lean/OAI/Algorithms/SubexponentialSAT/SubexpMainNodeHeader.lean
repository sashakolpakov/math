import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutPorts
import OAI.Algorithms.SubexponentialSAT.SubexpSetupFrames
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedSetupBounds
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

namespace OAI.Algorithms

/-!
# Physical header for the node traversal

After the source row table is built, this fixed program copies target zero,
target one, target minus one, and the actual unary R+1 counter into the node
worker's retained ports. Every destination is cleared before copying. The
source words, source cache, row table, and pending leaf stream are preserved.
-/

namespace SubexponentialSAT.SubexpMainNodeHeader

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupStorage

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 16 9
abbrev Code := Cmd 16 9

def sources : Fin 4 → Fin 9 := ![0, 1, 2, 3]
def targets : Fin 4 → Fin 9 := ![4, 5, 6, 7]
def temporary : Fin 9 := 8
def copies : List (Fin 9 × Fin 9) := [(0, 4), (1, 5), (2, 6), (3, 7)]
def cleared : List (Fin 9) := [4, 5, 6, 7]

theorem copies_good : ∀ q ∈ copies,
    q.1 ≠ q.2 ∧ q.1 ≠ temporary ∧ temporary ≠ q.2 := by
  intro q hq
  simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> decide

theorem copies_separated : ∀ q ∈ copies, ∀ z ∈ copies, q.1 ≠ z.2 := by
  intro q hq z hz
  simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hq hz
  rcases hq with rfl | rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl | rfl <;> decide

def prepared (a : Data) : Data := clearManyState cleared (clearManyState [temporary] a)
def copied (a : Data) : Data := copyManyState copies (prepared a)
def result (a : Data) : Data := RegisterResetProgram.zeroed (copied a)

def command : Code := .seq (clearMany [temporary])
  (.seq (clearMany cleared) (.seq (copyMany temporary copies) RegisterResetProgram.all))
abbrev program : Program 16 9 (size command + 1) := compiled command 0 4

def cost (a : Data) : ℕ := clearManyCost [temporary] a +
  (clearManyCost cleared (clearManyState [temporary] a) +
    (copyManyCost copies (prepared a) + 16))

theorem prepared_temporary (a : Data) : (prepared a).stacks temporary = [] := by
  simp [prepared, clearMany_stacks, cleared, temporary]

theorem prepared_source (a : Data) (i : Fin 4) :
    (prepared a).stacks (sources i) = a.stacks (sources i) := by
  fin_cases i <;> simp [prepared, clearMany_stacks, cleared, temporary, sources]

theorem command_eval (a : Data) : Eval command (cost a) a (result a) :=
  (clearMany_eval [temporary] a).seq
    ((clearMany_eval cleared (clearManyState [temporary] a)).seq
      ((copyMany_eval temporary copies (prepared a) copies_good (prepared_temporary a)).seq
        (RegisterResetProgram.all_eval (copied a))))

theorem result_target (a : Data) (i : Fin 4) :
    (result a).stacks (targets i) = a.stacks (sources i) := by
  have hp : (sources i, targets i) ∈ copies := by fin_cases i <;> simp [sources, targets, copies]
  have hc : ∀ q ∈ copies, (prepared a).stacks q.2 = [] := by
    intro q hq
    simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;>
      simp [prepared, cleared, clearMany_stacks]
  exact (copyMany_value copies (prepared a) (by decide) hc copies_separated
    (sources i, targets i) hp).trans (prepared_source a i)

theorem result_frame (a : Data) (i : Fin 9) (hi : i ∉ cleared) (ht : i ≠ temporary) :
    (result a).stacks i = a.stacks i := by
  have ho : ∀ q ∈ copies, i ≠ q.2 := by
    intro q hq he
    apply hi
    rw [he]
    simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp [cleared]
  change (copyManyState copies (prepared a)).stacks i = _
  rw [copyMany_frame copies (prepared a) i ho]
  simp [prepared, clearMany_stacks, hi, ht]

theorem result_temporary (a : Data) : (result a).stacks temporary = [] := by
  change (copyManyState copies (prepared a)).stacks temporary = _
  rw [copyMany_frame copies (prepared a) temporary (by
    intro q hq
    exact (copies_good q hq).2.2)]
  exact prepared_temporary a

theorem data_bound (a : Data) :
    SubexpPreparedSetupCalls.StackBound a (BitProgram.stackBits a.stacks) := by
  intro i
  exact Finset.single_le_sum (fun (j : Fin 9) _ => Nat.zero_le (a.stacks j).length)
    (Finset.mem_univ i)

theorem cost_le (a : Data) : cost a ≤ 100 * (BitProgram.stackBits a.stacks + 1) := by
  have h1 := SubexpPreparedSetupCalls.clearManyCost_le [temporary] a (data_bound a)
  have hp := SubexpPreparedSetupCalls.clearMany_bound [temporary] a (data_bound a)
  have h2 := SubexpPreparedSetupCalls.clearManyCost_le cleared (clearManyState [temporary] a) hp
  have hc : SubexpPreparedSetupCalls.StackBound (prepared a) (BitProgram.stackBits a.stacks) :=
    SubexpPreparedSetupCalls.clearMany_bound cleared _ hp
  have h3 := SubexpPreparedSetupCalls.copyManyCost_le copies (prepared a)
    (fun q _ => hc q.1) copies_separated
  have hn : cleared.length = 4 := rfl
  have hm : copies.length = 4 := rfl
  simp only [List.length_singleton, one_mul] at h1
  rw [hn] at h2
  rw [hm] at h3
  unfold cost
  omega

def sourcePort {es : ℕ} (a : SubexpLayoutPorts.Allocation es) : Fin 4 → Fin (totalStacks es) :=
  ![persistent es 28, persistent es 30, persistent es 31, SubexpLayoutPorts.ordinary a 243]
def targetPort {es : ℕ} (a : SubexpLayoutPorts.Allocation es) : Fin 4 → Fin (totalStacks es) :=
  ![SubexpLayoutPorts.ordinary a 119, SubexpLayoutPorts.ordinary a 120,
    SubexpLayoutPorts.ordinary a 121, SubexpLayoutPorts.ordinary a 126]

def stackMap {es : ℕ} (a : SubexpLayoutPorts.Allocation es) : Fin 9 → Fin (totalStacks es) :=
  ![persistent es 28, persistent es 30, persistent es 31, SubexpLayoutPorts.ordinary a 243,
    SubexpLayoutPorts.ordinary a 119, SubexpLayoutPorts.ordinary a 120,
    SubexpLayoutPorts.ordinary a 121, SubexpLayoutPorts.ordinary a 126,
    SubexpLayoutPorts.ordinary a 319]

theorem stackMap_injective {es : ℕ} (a : SubexpLayoutPorts.Allocation es) :
    Function.Injective (stackMap a) := by
  intro i j hij
  have h := congrArg Fin.val hij
  have hw := a.enough.trans a.within
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals norm_num [stackMap, persistent, SubexpLayoutPorts.ordinary] at h <;> omega

@[simp] theorem stackMap_source {es : ℕ} (a : SubexpLayoutPorts.Allocation es) (i : Fin 4) :
    stackMap a (sources i) = sourcePort a i := by fin_cases i <;> rfl
@[simp] theorem stackMap_target {es : ℕ} (a : SubexpLayoutPorts.Allocation es) (i : Fin 4) :
    stackMap a (targets i) = targetPort a i := by fin_cases i <;> rfl

def procedure (er : ℕ) {es : ℕ} (a : SubexpLayoutPorts.Allocation es) : Procedure er es where
  registers := 16
  stackCount := 9
  labels := size command + 1
  program := program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin (workRegs er) => k.val) h)⟩
  stack := ⟨stackMap a, stackMap_injective a⟩

noncomputable def installed {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) : MainState er es :=
  (procedure er alloc).install a (result ((procedure er alloc).project a))

theorem installed_target {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (i : Fin 4) :
    (installed alloc a).stacks (targetPort alloc i) = a.stacks (sourcePort alloc i) := by
  have h := (embedState_stack (procedure er alloc).registerMap (procedure er alloc).stack
    a (result ((procedure er alloc).project a)) (procedure er alloc).stack.injective (targets i)).trans
      (result_target ((procedure er alloc).project a) i)
  change (installed alloc a).stacks (stackMap alloc (targets i)) = a.stacks (stackMap alloc (sources i)) at h
  simpa only [stackMap_source, stackMap_target] using h

theorem installed_frame {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (j : Fin (totalStacks es))
    (ht : ∀ i, targetPort alloc i ≠ j)
    (hs : SubexpLayoutPorts.ordinary alloc 319 ≠ j) :
    (installed alloc a).stacks j = a.stacks j := by
  by_cases hm : ∃ i, stackMap alloc i = j
  · obtain ⟨i, rfl⟩ := hm
    have hi : i ∉ cleared := by
      intro hmem
      simp only [cleared, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      · exact ht 0 rfl
      · exact ht 1 rfl
      · exact ht 2 rfl
      · exact ht 3 rfl
    have hi8 : i ≠ temporary := by
      intro he
      subst i
      exact hs rfl
    exact (embedState_stack (procedure er alloc).registerMap (procedure er alloc).stack a
      (result ((procedure er alloc).project a)) (procedure er alloc).stack.injective i).trans
      (result_frame ((procedure er alloc).project a) i hi hi8)
  · exact embedState_stack_frame _ _ _ _ _ hm

theorem installed_control {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (i : Fin 3) :
    (installed alloc a).regs (controlRegister er i) = a.regs (controlRegister er i) :=
  Procedure.install_control _ _ _ _

def runtimeBound {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) : ℕ := 100 * (BitProgram.stackBits ((procedure er alloc).project a).stacks + 1) + 1

/-- The bound depends on the nine actually selected words, including old
destination contents that the program physically clears. -/
theorem execution {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) (a : MainState er es) :
    ∃ n ≤ runtimeBound alloc a, Eval (procedure er alloc).invoke n a (installed alloc a) := by
  refine ⟨cost ((procedure er alloc).project a) + 1, Nat.add_le_add_right (cost_le _) 1, ?_⟩
  exact Procedure.invoke_trace _ _ _ (compiled_halt_trace (command_eval _) 0 4)

end SubexponentialSAT.SubexpMainNodeHeader

end OAI.Algorithms
