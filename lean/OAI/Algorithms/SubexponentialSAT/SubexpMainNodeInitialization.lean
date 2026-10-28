import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentPorts
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWideInitialization

namespace OAI.Algorithms

/-!
# Actual widened node initialization in the Main allocation

The fixed initializer reads the retained unary dimension through static
port264, builds its local numeric/literal/slot masters, and copies the actual
target-node record stream. Its scratch precondition is stated directly on
the finite physical ports so the post-row clear can discharge it.
-/

namespace SubexponentialSAT.SubexpMainNodeInitialization

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation master ordinary)

attribute [local simp] Fin.coe_ofNat_eq_mod

def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 16
  stackCount := 352
  labels := size SubexpNodeWideInitialization.command + 1
  program := SubexpNodeWideInitialization.program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun q : Fin (workRegs er) => q.val) h)⟩
  stack := ⟨SubexpMainMomentPorts.stackMap alloc, SubexpMainMomentPorts.stackMap_injective alloc⟩

def projected {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    SubexpNodeWideSetup.Data :=
  (procedure er alloc).project a

def NeedsEmpty (i : Fin 352) : Prop :=
  i = 0 ∨ i = 1 ∨ i = 4 ∨
  (112 ≤ i.val ∧ i.val ≤ 116) ∨ (122 ≤ i.val ∧ i.val ≤ 124) ∨
  (138 ≤ i.val ∧ i.val ≤ 152) ∨ (200 ≤ i.val ∧ i.val ≤ 216) ∨
  (248 ≤ i.val ∧ i.val ≤ 254) ∨ i = 337

instance (i : Fin 352) : Decidable (NeedsEmpty i) := by
  unfold NeedsEmpty
  infer_instance

/-- All scratch words are among the explicitly cleared physical ports.
No setup algorithm or unbounded semantic test is hidden in this predicate. -/
theorem ready_of_empty (d : SubexpNodeWideSetup.Data)
    (hempty : ∀ i, NeedsEmpty i → d.stacks i = [])
    (hwidth : 0 < (d.stacks 10).length) : SubexpNodeWideInitialization.Ready d := by
  refine ⟨hempty 0 (by decide), hempty 1 (by decide), hempty 4 (by decide), ?_, ?_,
    hempty 122 (by decide), hempty 123 (by decide), hempty 124 (by decide),
    hwidth, hempty 337 (by decide), ?_⟩
  · intro i hi
    change d.stacks (SubexpNodeWideSetup.lowPorts i) = []
    apply hempty
    simp only [SubexpNodeExponentMaster.work, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro i hlo hhi
    change d.stacks (SubexpNodeWideSetup.lowPorts i) = []
    apply hempty
    unfold NeedsEmpty SubexpNodeWideSetup.lowPorts
    simp only [Fin.val_castAdd]
    omega
  · refine ⟨hempty 140 (by decide), hempty 139 (by decide), hempty 141 (by decide), ?_⟩
    intro i hi
    change d.stacks (SubexpNodeWideSetup.lowPorts (SubexpNodeJobsStage.port i)) = []
    apply hempty
    simp only [SubexpSlotSetup.work, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem projected_dimension {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    (projected alloc a).stacks 264 = a.stacks (master alloc 8) := by
  change a.stacks (SubexpMainMomentPorts.stackMap alloc 264) = _
  exact congrArg a.stacks (SubexpMainMomentPorts.stackMap_static alloc 8)

theorem projected_width {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    (projected alloc a).stacks 10 = a.stacks (persistent es 13) := by
  change a.stacks (SubexpMainMomentPorts.stackMap alloc 10) = _
  rw [SubexpMainMomentPorts.stackMap_width]

def runtimeBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es) (D : ℕ) : ℕ :=
  SubexpNodeWideInitialization.budget (projected alloc a) D + 1

structure Result {er es : ℕ} (alloc : Allocation es) (a b : MainState er es) (D : ℕ) : Prop where
  words : ∀ i, b.stacks (SubexpMainMomentPorts.stackMap alloc i) =
    SubexpNodeWideInitialization.resultStacks (projected alloc a) D i
  frame : ∀ i, (¬ ∃ j, SubexpMainMomentPorts.stackMap alloc j = i) → b.stacks i = a.stacks i
  controls : ∀ i, b.regs (controlRegister er i) = a.regs (controlRegister er i)

/-- This invokes the actual dimension, exponent, literal, target-node, and
slot generators. Only their finite scratch and retained dimension are inputs. -/
theorem execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es) (D : ℕ)
    (hempty : ∀ i, NeedsEmpty i → (projected alloc a).stacks i = [])
    (hwidth : 0 < (a.stacks (persistent es 13)).length)
    (hD : a.stacks (master alloc 8) = List.replicate D true) :
    ∃ n ≤ runtimeBound alloc a D, ∃ b,
      Eval (procedure er alloc).invoke n a b ∧ Result alloc a b D := by
  have hw : 0 < ((projected alloc a).stacks 10).length := by
    rw [projected_width]
    exact hwidth
  have hd : (projected alloc a).stacks 264 = List.replicate D true :=
    (projected_dimension alloc a).trans hD
  obtain ⟨out, ⟨n, hn, ht⟩, hs⟩ := SubexpNodeWideInitialization.program_runs
    (projected alloc a) D (ready_of_empty _ hempty hw) hd
  refine ⟨n, hn, (procedure er alloc).install a out, Procedure.invoke_trace _ _ _ ht, ?_⟩
  refine ⟨?_, ?_, Procedure.install_control _ _ _⟩
  · intro i
    exact (embedState_stack (procedure er alloc).registerMap (procedure er alloc).stack
      a out (procedure er alloc).stack.injective i).trans (congrFun hs i)
  · intro i hi
    exact embedState_stack_frame _ _ _ _ _ hi

theorem Result.static_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es} {D : ℕ}
    (h : Result alloc a b D) (i : Fin 32) : b.stacks (master alloc i) = a.stacks (master alloc i) := by
  let j : Fin 352 := ⟨256 + i.val, by omega⟩
  have hj := h.words j
  have hm : SubexpMainMomentPorts.stackMap alloc j = master alloc i :=
    SubexpMainMomentPorts.stackMap_static alloc i
  rw [hm] at hj
  have hv (q : Fin 352) (hq : q.val < 256) : j ≠ q := by
    intro he
    have he' := congrArg (fun z : Fin 352 => z.val) he
    dsimp [j] at he'
    omega
  have hstack : (procedure er alloc).stack j = master alloc i := by
    change SubexpMainMomentPorts.stackMap alloc j = master alloc i
    exact hm
  have hj' : b.stacks (master alloc i) =
      a.stacks ((procedure er alloc).stack j) := by
    simpa [SubexpNodeWideInitialization.resultStacks, SubexpNodeWideSetup.resultStacks,
      SubexpNodeWideSetup.localResult, SubexpNodeWideInitialization.dimensionResult,
      hv 25 (by decide), hv 92 (by decide), hv 109 (by decide), hv 122 (by decide),
      hv 123 (by decide), hv 124 (by decide), hv 125 (by decide), hv 127 (by decide),
      projected, Procedure.project, projectState, procedure] using hj
  exact hj'.trans (congrArg a.stacks hstack)

end SubexponentialSAT.SubexpMainNodeInitialization

end OAI.Algorithms
