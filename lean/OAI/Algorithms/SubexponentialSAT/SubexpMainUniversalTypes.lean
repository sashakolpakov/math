import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalTypeProgram
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedSetupBounds
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutPorts
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram

namespace OAI.Algorithms

/-! Actual universal-type generation in Main's retained layout storage. -/

namespace SubexponentialSAT.SubexpMainUniversalTypes

open BitProgram StructuredCalls SubexpSetupStorage SubexpMainProgram Subexp
open SubexpPreparedSetupCalls (StackBound)
open SubexpLayoutPorts (Allocation master ordinary)
open scoped BigOperators

attribute [local simp] Fin.coe_ofNat_eq_mod Fin.ext_iff

namespace Staging

abbrev Data := State 16 13
abbrev Command := Cmd 16 13

def register : Fin 10 → Fin 16 := Fin.castAdd 6
def callee : Fin 9 → Fin 13 := Fin.castAdd 4
def work : List (Fin 13) := List.ofFn callee
def inputs : List (Fin 13 × Fin 13) := [(9, 1), (10, 8)]
def outputs : List (Fin 13 × Fin 13) := [(0, 11)]

theorem register_injective : Function.Injective register := Fin.castAdd_injective 10 6
theorem callee_injective : Function.Injective callee := Fin.castAdd_injective 9 4

theorem mem_work (j : Fin 13) : j ∈ work ↔ j.val < 9 := by
  simp only [work, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact i.isLt
  · intro hj
    exact ⟨⟨j.val, hj⟩, Fin.ext rfl⟩

theorem inputs_good : ∀ p ∈ inputs,
    p.1 ≠ p.2 ∧ p.1 ≠ 12 ∧ (12 : Fin 13) ≠ p.2 := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · decide
  · rcases List.mem_singleton.mp hp with rfl
    decide

theorem outputs_good : ∀ p ∈ outputs,
    p.1 ≠ p.2 ∧ p.1 ≠ 12 ∧ (12 : Fin 13) ≠ p.2 := by
  intro p hp
  rcases List.mem_singleton.mp hp with rfl
  decide

def prepared (a : Data) : Data := prepareState 12 work inputs a

theorem prepared_project (a : Data) (r Q Δ : ℕ)
    (ha : a.stacks 9 = ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes r Q))
    (hd : a.stacks 10 = List.replicate Δ true) :
    project register callee (prepared a) = UniversalTypeProgram.inputState
      (AssignmentAlphabetSemantics.wordBytes r Q) (List.replicate Δ true)
      ((prepared a).regs ∘ register) := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  simp only [Function.comp_apply]
  fin_cases i <;>
    simp [prepared, prepareState, inputs,
      copyManyState, copyState, StackRoutines.copyStacks, beforeCopies,
      resetMany_stacks, clearMany_stacks, mem_work, callee, ha, hd]

def command : Command := .seq (prepare 12 work inputs)
  (.seq (invoke UniversalTypeProgram.program register callee)
    (.seq (finish 12 work outputs) RegisterResetProgram.all))

abbrev program : Program 16 13 (size command + 1) := compiled command 9 11

def wordBound (a : Data) : ℕ := ∑ j : Fin 13, (a.stacks j).length

theorem wordBound_spec (a : Data) : StackBound a (wordBound a) := by
  intro j
  change (a.stacks j).length ≤ ∑ i : Fin 13, (a.stacks i).length
  exact Finset.single_le_sum (f := fun i : Fin 13 => (a.stacks i).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

def prefixBudget (a : Data) (r Q Δ : ℕ) : ℕ :=
  prepareCost 12 work inputs a +
    UniversalTypeProgram.budget (AssignmentAlphabetSemantics.wordBytes r Q) Δ

def runtimeBound (a : Data) (r Q Δ : ℕ) : ℕ :=
  prefixBudget a r Q Δ + 100 * (wordBound a + prefixBudget a r Q Δ + 2) + 1

theorem finish_cost_le (a : Data) (W : ℕ) (ha : StackBound a W) :
    finishCost work outputs a + 16 ≤ 100 * (W + 1) := by
  let cleared := clearManyState [11] a
  have hc : StackBound cleared W := SubexpPreparedSetupCalls.clearMany_bound [11] a ha
  have hcopy : StackBound (copyManyState outputs cleared) W := by
    apply SubexpPreparedSetupCalls.copyMany_bound outputs cleared hc
    · decide
    · intro p hp
      rcases List.mem_singleton.mp hp with rfl
      simp [cleared, clearMany_stacks]
    · intro p hp q hq
      rcases List.mem_singleton.mp hp with rfl
      rcases List.mem_singleton.mp hq with rfl
      decide
  have h1 := SubexpPreparedSetupCalls.clearManyCost_le [11] a ha
  have h2 := SubexpPreparedSetupCalls.copyManyCost_le outputs cleared
    (fun p _ => hc p.1) (by
      intro p hp q hq
      rcases List.mem_singleton.mp hp with rfl
      rcases List.mem_singleton.mp hq with rfl
      decide)
  have h3 := SubexpPreparedSetupCalls.clearManyCost_le work (copyManyState outputs cleared) hcopy
  have hw : work.length = 9 := by simp [work]
  have ho : outputs.length = 1 := rfl
  rw [ho, one_mul] at h2
  simp only [List.length_singleton, one_mul] at h1
  rw [hw] at h3
  change clearManyCost [11] a +
    (copyManyCost outputs cleared + (clearManyCost work (copyManyState outputs cleared) + 9)) + 16 ≤ _
  omega

structure Result (a b : Data) (r Q Δ : ℕ) : Prop where
  output : b.stacks 11 = ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ)
  alphabet : b.stacks 9 = a.stacks 9
  delta : b.stacks 10 = a.stacks 10
  scratch : ∀ j : Fin 13, j.val < 9 → b.stacks j = []
  temporary : b.stacks 12 = []
  registers : ∀ i, b.regs i = false

theorem run (a : Data) (r Q Δ : ℕ)
    (ha : a.stacks 9 = ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes r Q))
    (hd : a.stacks 10 = List.replicate Δ true) :
    ∃ b, RunsIn program (runtimeBound a r Q Δ)
      (a.withPC (some program.entry)) (b.withPC none) ∧ Result a b r Q Δ := by
  have hp := prepare_eval 12 work inputs a inputs_good
  have hproject := prepared_project a r Q Δ ha hd
  obtain ⟨rf, t, ht, htrace⟩ := UniversalTypeProgram.universal_runsIn r Q Δ
    ((prepared a).regs ∘ register)
  rw [← hproject] at htrace
  let out := UniversalTypeProgram.outputState (AssignmentAlphabetSemantics.wordBytes r Q)
    (TypeEnumeration.universalBytes r Q Δ) rf
  let middle := embedState register callee (prepared a) out
  have hi : Eval (invoke UniversalTypeProgram.program register callee) t (prepared a) middle :=
    invoke_eval _ _ _ register_injective callee_injective (prepared a) out htrace
  have hlow (i : Fin 9) : middle.stacks (callee i) = out.stacks i :=
    embedState_stack register callee (prepared a) out callee_injective i
  have hhigh (j : Fin 13) (hj : 9 ≤ j.val) : middle.stacks j = (prepared a).stacks j := by
    apply embedState_stack_frame
    rintro ⟨i, he⟩
    have hv := congrArg (fun z : Fin 13 => z.val) he
    change i.val = j.val at hv
    omega
  have htmp : middle.stacks 12 = [] := by
    rw [hhigh 12 (by decide)]
    exact prepare_temporary 12 work inputs a inputs_good
  have hf := finish_eval 12 work outputs middle outputs_good htmp
  let b := RegisterResetProgram.zeroed (finishState work outputs middle)
  have hall := RegisterResetProgram.all_eval (finishState work outputs middle)
  let W := wordBound a + prefixBudget a r Q Δ + 1
  have hm : StackBound middle W := by
    intro j
    have hg := SequentialProgram.trace_stack_length_le (compiled_halt_trace (hp.seq hi) 9 11) j
    have hw := wordBound_spec a j
    change (middle.stacks j).length ≤ (a.stacks j).length +
      (prepareCost 12 work inputs a + t + 1) at hg
    dsimp [W, prefixBudget]
    omega
  have hc := finish_cost_le middle W hm
  refine ⟨b, ⟨prepareCost 12 work inputs a + (t + (finishCost work outputs middle + 16)) + 1,
    ?_, compiled_halt_trace (hp.seq (hi.seq (hf.seq hall))) 9 11⟩, ?_⟩
  · dsimp [runtimeBound, prefixBudget, W] at *
    omega
  · have hretain (j : Fin 13) (hj : j = 9 ∨ j = 10) : b.stacks j = a.stacks j := by
      change (finishState work outputs middle).stacks j = _
      rcases hj with rfl | rfl
      all_goals
        rw [finish_frame work outputs middle _ (by rw [mem_work]; decide)
          (by intro p hp; rcases List.mem_singleton.mp hp with rfl; decide),
          hhigh _ (by decide)]
        exact prepare_frame 12 work inputs a _ (by decide) (by rw [mem_work]; decide)
          (by intro p hp; rcases List.mem_cons.mp hp with rfl | hp
              · decide
              · rcases List.mem_singleton.mp hp with rfl; decide)
    constructor
    · change (finishState work outputs middle).stacks 11 = _
      exact (finish_value work outputs middle (by decide)
        (by intro p hp q hq
            rcases List.mem_singleton.mp hp with rfl
            rcases List.mem_singleton.mp hq with rfl
            decide) (0, 11) (by simp [outputs]) (by rw [mem_work]; decide)).trans (hlow 0)
    · exact hretain 9 (Or.inl rfl)
    · exact hretain 10 (Or.inr rfl)
    · intro j hj
      exact finish_empty work outputs middle j ((mem_work j).mpr hj)
    · exact (finish_frame work outputs middle 12 (by rw [mem_work]; decide)
        (by intro p hp; rcases List.mem_singleton.mp hp with rfl; decide)).trans htmp
    · intro i; rfl

end Staging

def masterIndex : Fin 3 → Fin 32 := ![3, 7, 10]

theorem masterIndex_injective : Function.Injective masterIndex := by decide

def stackMap {es : ℕ} (alloc : Allocation es) (i : Fin 13) : Fin (totalStacks es) :=
  if hw : i.val < 9 ∨ i.val = 12 then ordinary alloc ⟨i.val, by omega⟩
  else master alloc (masterIndex ⟨i.val - 9, by omega⟩)

theorem stackMap_injective {es : ℕ} (alloc : Allocation es) : Function.Injective (stackMap alloc) := by
  intro i j he
  have hv := congrArg (fun z : Fin (totalStacks es) => z.val) he
  by_cases hi : i.val < 9 ∨ i.val = 12 <;> by_cases hj : j.val < 9 ∨ j.val = 12
  · apply Fin.ext
    simpa only [stackMap, dite_eq_left hi, dite_eq_left hj, ordinary] using hv
  · simp only [stackMap, dite_eq_left hi, dite_eq_right hj, ordinary, SubexpLayoutPorts.master_val] at hv
    omega
  · simp only [stackMap, dite_eq_right hi, dite_eq_left hj, ordinary, SubexpLayoutPorts.master_val] at hv
    omega
  · have hm := SubexpLayoutPorts.master_injective alloc (by
      simpa only [stackMap, dite_eq_right hi, dite_eq_right hj] using he)
    have hm' := congrArg (fun z : Fin 3 => z.val) (masterIndex_injective hm)
    apply Fin.ext
    dsimp only at hm'
    omega

@[simp] theorem stackMap_callee {es : ℕ} (alloc : Allocation es) (i : Fin 9) :
    stackMap alloc (Staging.callee i) = ordinary alloc ⟨i.val, by omega⟩ := by
  unfold stackMap
  have hw : (Staging.callee i).val < 9 ∨ (Staging.callee i).val = 12 :=
    Or.inl i.isLt
  rw [dite_eq_left hw]
  apply congrArg (ordinary alloc)
  exact Fin.ext rfl

@[simp] theorem stackMap_alphabet {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 9 = master alloc 3 := rfl
@[simp] theorem stackMap_delta {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 10 = master alloc 7 := rfl
@[simp] theorem stackMap_output {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 11 = master alloc 10 := rfl
@[simp] theorem stackMap_temporary {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 12 = ordinary alloc 12 := rfl

theorem stackMap_below_cleanup {es : ℕ} (alloc : Allocation es) (i : Fin 13) :
    (stackMap alloc i).val < alloc.ordinaryCount := by
  by_cases hi : i.val < 9 ∨ i.val = 12
  · have hn := alloc.enough
    simp only [stackMap, dite_eq_left hi, ordinary]
    omega
  · simp only [stackMap, dite_eq_right hi]
    exact SubexpLayoutPorts.master_below_cleanup alloc _

theorem stackMap_avoids_master {es : ℕ} (alloc : Allocation es) (i : Fin 32)
    (h3 : i ≠ 3) (h7 : i ≠ 7) (h10 : i ≠ 10) :
    ¬ ∃ j, stackMap alloc j = master alloc i := by
  rintro ⟨j, hj⟩
  by_cases hw : j.val < 9 ∨ j.val = 12
  · have hv := congrArg (fun z : Fin (totalStacks es) => z.val) hj
    simp only [stackMap, dite_eq_left hw, ordinary, SubexpLayoutPorts.master_val] at hv
    omega
  · have he := SubexpLayoutPorts.master_injective alloc (by
      simpa only [stackMap, dite_eq_right hw] using hj)
    have hall : ∀ k, masterIndex k = 3 ∨ masterIndex k = 7 ∨ masterIndex k = 10 := by decide
    rcases hall ⟨j.val - 9, by omega⟩ with h | h | h
    · exact h3 (he.symm.trans h)
    · exact h7 (he.symm.trans h)
    · exact h10 (he.symm.trans h)

def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 16
  stackCount := 13
  labels := size Staging.command + 1
  program := Staging.program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j he
    exact Fin.ext (congrArg (fun z : Fin (workRegs er) => z.val) he)⟩
  stack := ⟨stackMap alloc, stackMap_injective alloc⟩

def program (er : ℕ) {es : ℕ} (alloc : Allocation es) :=
  ProgramLinking.liftProgram (procedure er alloc).program
    (procedure er alloc).registerMap (procedure er alloc).stack

structure Result {er es : ℕ} (alloc : Allocation es) (a b : MainState er es) (r Q Δ : ℕ) : Prop where
  output : b.stacks (master alloc 10) = ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ)
  alphabet : b.stacks (master alloc 3) = a.stacks (master alloc 3)
  delta : b.stacks (master alloc 7) = a.stacks (master alloc 7)
  scratch : ∀ i : Fin 9, b.stacks (ordinary alloc ⟨i.val, by omega⟩) = []
  temporary : b.stacks (ordinary alloc 12) = []
  frame : ∀ j, (¬ ∃ i, stackMap alloc i = j) → b.stacks j = a.stacks j
  registers : ∀ i : Fin 16, b.regs ((procedure er alloc).registerMap i) = false
  registerFrame : ∀ j, (¬ ∃ i, (procedure er alloc).registerMap i = j) → b.regs j = a.regs j
  controls : ∀ i, b.regs (controlRegister er i) = a.regs (controlRegister er i)

namespace Result

theorem master_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es} {r Q Δ : ℕ}
    (h : Result alloc a b r Q Δ) (i : Fin 32) (hi : i ≠ 10) :
    b.stacks (master alloc i) = a.stacks (master alloc i) := by
  by_cases h3 : i = 3
  · subst i; exact h.alphabet
  by_cases h7 : i = 7
  · subst i; exact h.delta
  exact h.frame _ (stackMap_avoids_master alloc i h3 h7 hi)

theorem persistent_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es} {r Q Δ : ℕ}
    (h : Result alloc a b r Q Δ) (i : Fin 32) :
    b.stacks (persistent es i) = a.stacks (persistent es i) := by
  apply h.frame
  rintro ⟨j, hj⟩
  have hv := congrArg (fun z : Fin (totalStacks es) => z.val) hj
  have hl := stackMap_below_cleanup alloc j
  have hn := alloc.within
  simp only [persistent, Fin.val_natAdd] at hv
  omega

theorem work_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es} {r Q Δ : ℕ}
    (h : Result alloc a b r Q Δ) (i : Fin (totalStacks es))
    (hlo : 13 ≤ i.val) (hhi : i.val < 640) : b.stacks i = a.stacks i := by
  apply h.frame
  rintro ⟨j, hj⟩
  have hv := congrArg (fun z : Fin (totalStacks es) => z.val) hj
  by_cases hw : j.val < 9 ∨ j.val = 12
  · simp only [stackMap, dite_eq_left hw, ordinary] at hv
    omega
  · simp only [stackMap, dite_eq_right hw, SubexpLayoutPorts.master_val] at hv
    omega

theorem threshold_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es} {r Q Δ : ℕ}
    (h : Result alloc a b r Q Δ) (i : Fin (totalStacks es))
    (hlo : alloc.ordinaryCount ≤ i.val) : b.stacks i = a.stacks i := by
  apply h.frame
  rintro ⟨j, hj⟩
  have hl := stackMap_below_cleanup alloc j
  rw [hj] at hl
  omega

theorem enumeration {er es : ℕ} {alloc : Allocation es} {a b : MainState er es} {r Q Δ : ℕ}
    (h : Result alloc a b r Q Δ) (hr : 0 < r) (hQ : 0 < Q) :
    ∃ us : List (MulticolorTypes.UniversalType r Q Δ),
      b.stacks (master alloc 10) = ProgramEncoding.encodeRecords (us.map CollisionProgram.encodeType) ∧
      us.Nodup ∧ ∀ u, u ∈ us := by
  obtain ⟨us, he, hn, hf⟩ := TypeEnumeration.universalBytes_order hr hQ Δ
  exact ⟨us, h.output.trans (congrArg ProgramEncoding.encodeRecords he.symm), hn, hf⟩

end Result

theorem install_result {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : Staging.Data) (r Q Δ : ℕ)
    (h : Staging.Result ((procedure er alloc).project a) out r Q Δ) :
    Result alloc a ((procedure er alloc).install a out) r Q Δ := by
  have hs (i : Fin 13) := embedState_stack (procedure er alloc).registerMap
    (procedure er alloc).stack a out (procedure er alloc).stack.injective i
  constructor
  · exact (hs 11).trans h.output
  · exact (hs 9).trans h.alphabet
  · exact (hs 10).trans h.delta
  · intro i
    have hi := hs (Staging.callee i)
    change ((procedure er alloc).install a out).stacks (stackMap alloc _) = _ at hi
    rw [stackMap_callee] at hi
    exact hi.trans (h.scratch _ i.isLt)
  · exact (hs 12).trans h.temporary
  · intro j hj; exact embedState_stack_frame _ _ _ _ _ hj
  · intro i
    exact (embedState_register _ _ _ _ (procedure er alloc).registerMap_injective i).trans (h.registers i)
  · intro j hj; exact embedState_register_frame _ _ _ _ _ hj
  · exact Procedure.install_control _ _ _

def runtimeBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es) (r Q Δ : ℕ) : ℕ :=
  Staging.runtimeBound ((procedure er alloc).project a) r Q Δ

theorem execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es) (r Q Δ : ℕ)
    (ha : a.stacks (master alloc 3) = ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes r Q))
    (hd : a.stacks (master alloc 7) = List.replicate Δ true) :
    ∃ n ≤ runtimeBound alloc a r Q Δ, ∃ b,
      Eval (procedure er alloc).invoke n a b ∧ Result alloc a b r Q Δ := by
  obtain ⟨out, ⟨n, hn, ht⟩, hr⟩ := Staging.run ((procedure er alloc).project a) r Q Δ ha hd
  exact ⟨n, hn, (procedure er alloc).install a out, Procedure.invoke_trace _ _ _ ht,
    install_result alloc a out r Q Δ hr⟩

theorem program_runsIn {er es : ℕ} (alloc : Allocation es) (a : MainState er es) (r Q Δ : ℕ)
    (ha : a.stacks (master alloc 3) = ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes r Q))
    (hd : a.stacks (master alloc 7) = List.replicate Δ true) :
    ∃ b, RunsIn (program er alloc) (runtimeBound alloc a r Q Δ)
      (a.withPC (some (program er alloc).entry)) (b.withPC none) ∧ Result alloc a b r Q Δ := by
  obtain ⟨n, hn, b, he, hr⟩ := execution alloc a r Q Δ ha hd
  refine ⟨b, ⟨n, hn, ?_⟩, hr⟩
  cases he with
  | call _ ht => exact ht

end SubexponentialSAT.SubexpMainUniversalTypes

end OAI.Algorithms
