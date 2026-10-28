import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutConstruction
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutPorts
import OAI.Algorithms.SubexponentialSAT.SubexpSetupFrames
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedSetupBounds

namespace OAI.Algorithms

/-!
# Main allocation for the concrete layout construction

The factor stage invokes the fixed raw-factor constructor, physically stores
the two resulting streams in the retained layout bank, and clears its local
work. The later assignment, search, packing, and row stages extend this same
controller as their concrete interfaces are published.
-/

namespace SubexponentialSAT.SubexpMainLayout

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupStorage

attribute [local simp] Fin.coe_ofNat_eq_mod

namespace Factors

abbrev Data := State 16 48
abbrev Code := Cmd 16 48

def temporary : Fin 48 := 47
def calleePort (i : Fin 45) : Fin 48 := i.castAdd 3
theorem calleePort_injective : Function.Injective calleePort := Fin.castAdd_injective 45 3

def workPorts : List (Fin 48) :=
  (List.finRange 48).filter (fun i => decide (i.val < 35 ∨ 40 ≤ i.val ∧ i.val < 45))

@[simp] theorem mem_workPorts (i : Fin 48) :
    i ∈ workPorts ↔ i.val < 35 ∨ 40 ≤ i.val ∧ i.val < 45 := by simp [workPorts]

def exports : List (Fin 48 × Fin 48) := [(33, 45), (32, 46)]

theorem exports_good : ∀ q ∈ exports,
    q.1 ≠ q.2 ∧ q.1 ≠ temporary ∧ temporary ≠ q.2 := by
  intro q h
  simp only [exports, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide

theorem exports_separated : ∀ q ∈ exports, ∀ z ∈ exports, q.1 ≠ z.2 := by
  intro q h z hz
  simp only [exports, List.mem_cons, List.not_mem_nil, or_false] at h hz
  rcases h with rfl | rfl <;> rcases hz with rfl | rfl <;> decide

def inputs (a : Data) : SubexpLayoutConstruction.Inputs :=
  ⟨⟨a.stacks 35, a.stacks 36, a.stacks 37, a.stacks 38⟩, a.stacks 39⟩

def prepared (a : Data) := prepareState temporary workPorts [] a

theorem prepared_entry (a : Data) :
    project id calleePort (prepared a) =
      SubexpLayoutRawPreparation.inputState (prepared a).regs (inputs a) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    simp only [Function.comp_apply]
    fin_cases i <;>
      simp [prepared, prepareState, beforeCopies, copyManyState,
        resetMany_stacks, clearMany_stacks, temporary, calleePort,
        inputs, Fin.coe_ofNat_eq_mod]

noncomputable def middle (a : Data) (b : SubexpLayoutConstruction.Data) : Data :=
  embedState id calleePort (prepared a) b

noncomputable def result (a : Data) (b : SubexpLayoutConstruction.Data) : Data :=
  RegisterResetProgram.zeroed (finishState workPorts exports (middle a b))

def command : Code := .seq
  (isolated SubexpLayoutConstruction.program id calleePort temporary workPorts [] exports)
  RegisterResetProgram.all

abbrev program : Program 16 48 (size command + 1) := compiled command 39 45

theorem data_bound (a : Data) :
    SubexpPreparedSetupCalls.StackBound a (BitProgram.stackBits a.stacks) := by
  intro i
  exact Finset.single_le_sum (fun (j : Fin 48) _ => Nat.zero_le (a.stacks j).length)
    (Finset.mem_univ i)

theorem prepared_bound (a : Data) :
    SubexpPreparedSetupCalls.StackBound (prepared a) (BitProgram.stackBits a.stacks) :=
  SubexpPreparedSetupCalls.beforeCopies_bound temporary workPorts a (data_bound a)

theorem prepareCost_bound (a : Data) :
    prepareCost temporary workPorts [] a ≤ 200 * (BitProgram.stackBits a.stacks + 1) := by
  have h1 := SubexpPreparedSetupCalls.clearManyCost_le [temporary] a (data_bound a)
  have h2 := SubexpPreparedSetupCalls.clearManyCost_le workPorts
    (clearManyState [temporary] a)
    (SubexpPreparedSetupCalls.clearMany_bound _ _ (data_bound a))
  have hlen : workPorts.length = 40 := by decide
  simp only [List.length_singleton, one_mul] at h1
  rw [hlen] at h2
  change clearManyCost [temporary] a +
    (clearManyCost workPorts (clearManyState [temporary] a) + (9 + 0)) ≤ _
  omega

theorem middle_bound (a : Data) (b : SubexpLayoutConstruction.Data) {T : ℕ}
    (hrun : RunsIn SubexpLayoutConstruction.program T
      ((project id calleePort (prepared a)).withPC
        (some SubexpLayoutConstruction.program.entry)) (b.withPC none)) :
    SubexpPreparedSetupCalls.StackBound (middle a b) (45 * BitProgram.stackBits a.stacks + T) := by
  have hi (i : Fin 45) :
      ((project id calleePort (prepared a)).stacks i).length ≤ BitProgram.stackBits a.stacks :=
    prepared_bound a (calleePort i)
  have his : BitProgram.stackBits (project id calleePort (prepared a)).stacks ≤
      45 * BitProgram.stackBits a.stacks := by
    change Nat.le (BitProgram.stackBits (project id calleePort (prepared a)).stacks)
      (45 * BitProgram.stackBits a.stacks)
    have h := Finset.sum_le_sum (fun (i : Fin 45) (_ : i ∈ Finset.univ) => hi i)
    simp only [BitProgram.stackBits, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h
    change Nat.le _ _ at h
    exact h
  have hg := BitProgram.runsIn_dataBits SubexpLayoutConstruction.program hrun
  change BitProgram.stackBits b.stacks ≤
    BitProgram.stackBits (project id calleePort (prepared a)).stacks + T at hg
  intro i
  by_cases hm : ∃ j, calleePort j = i
  · obtain ⟨j, rfl⟩ := hm
    have hj : (b.stacks j).length ≤ BitProgram.stackBits b.stacks :=
      Finset.single_le_sum (fun (k : Fin 45) _ => Nat.zero_le (b.stacks k).length)
        (Finset.mem_univ j)
    unfold middle
    rw [embedState_stack id calleePort _ b calleePort_injective]
    omega
  · unfold middle
    rw [embedState_stack_frame id calleePort _ b i hm]
    have h := prepared_bound a i
    omega

theorem finishCost_bound (a : Data) {W : ℕ}
    (ha : SubexpPreparedSetupCalls.StackBound a W) :
    finishCost workPorts exports a ≤ 200 * (W + 1) := by
  let b := clearManyState (exports.map Prod.snd) a
  have hb : SubexpPreparedSetupCalls.StackBound b W :=
    SubexpPreparedSetupCalls.clearMany_bound _ a ha
  have hc : SubexpPreparedSetupCalls.StackBound (copyManyState exports b) W := by
    apply SubexpPreparedSetupCalls.copyMany_bound _ b hb
    · decide
    · intro q hq
      dsimp [b]
      rw [clearMany_stacks, ite_eq_left (List.mem_map.mpr ⟨q, hq, rfl⟩)]
    · exact exports_separated
  have h1 := SubexpPreparedSetupCalls.clearManyCost_le (exports.map Prod.snd) a ha
  have h2 := SubexpPreparedSetupCalls.copyManyCost_le exports b
    (fun q _ => hb q.1) exports_separated
  have h3 := SubexpPreparedSetupCalls.clearManyCost_le workPorts _ hc
  have hout : exports.length = 2 := rfl
  have hlen : workPorts.length = 40 := by decide
  rw [List.length_map, hout] at h1
  rw [hout] at h2
  rw [hlen] at h3
  change clearManyCost (exports.map Prod.snd) a +
    (copyManyCost exports b + (clearManyCost workPorts (copyManyState exports b) + 9)) ≤ _
  omega

def localRuntimeBound (a : Data)
    (hv : SubexpClauseFamilyProgram.Valid (SubexpLayoutConstruction.familyInputs (inputs a))
      (SubexpLayoutConstruction.dimension (inputs a)) (SubexpLayoutConstruction.variableCount (inputs a)))
    (clauses : List (List (SAT.Literal (Fin (SubexpLayoutConstruction.variableCount (inputs a)))))) : ℕ :=
  10000 * (BitProgram.stackBits a.stacks +
    SubexpLayoutConstruction.runtimeBound (inputs a) hv clauses + 1)

def retained (i : Fin 5) : Fin 45 := ⟨35 + i.val, by omega⟩

theorem local_execution (a : Data)
    (hell : 0 < CounterPrograms.value (inputs a).counts.ell)
    (hwidth : CounterPrograms.value (inputs a).counts.ell ≤ (inputs a).counts.modulus.length)
    (hv : SubexpClauseFamilyProgram.Valid (SubexpLayoutConstruction.familyInputs (inputs a))
      (SubexpLayoutConstruction.dimension (inputs a)) (SubexpLayoutConstruction.variableCount (inputs a)))
    (clauses : List (List (SAT.Literal (Fin (SubexpLayoutConstruction.variableCount (inputs a))))))
    (hsource : (inputs a).leaf = Encoding.encodeList SubexpClauseRowProgram.clauseBytes clauses) :
    ∃ (b : SubexpLayoutConstruction.Data) (n : ℕ),
      Eval command n a (result a b) ∧
      b.stacks 32 = Encoding.encodeList id (SubexpLayoutConstruction.tables (inputs a) hv clauses) ∧
      b.stacks 33 = Encoding.encodeList id (SubexpLayoutConstruction.scopes (inputs a) clauses) ∧
      (∀ i, b.stacks (retained i) = a.stacks ((retained i).castAdd 3)) ∧
      n ≤ localRuntimeBound a hv clauses := by
  obtain ⟨b, ⟨t, ht, hrun⟩, h32, h33, _, _, _, hframe⟩ := SubexpLayoutConstruction.program_runs
    (prepared a).regs (inputs a) hell hwidth hv clauses hsource
  have hr : Trace SubexpLayoutConstruction.program t
      ((project id calleePort (prepared a)).withPC (some SubexpLayoutConstruction.program.entry))
      (b.withPC none) := by simpa only [prepared_entry] using hrun
  have he := isolated_eval SubexpLayoutConstruction.program id calleePort Function.injective_id
    calleePort_injective temporary workPorts [] exports a b (by simp) exports_good (by
      rintro ⟨j, hj⟩
      have hval := congrArg Fin.val hj
      change j.val = 47 at hval
      omega) hr
  have hz := RegisterResetProgram.all_eval (finishState workPorts exports (middle a b))
  refine ⟨b, _, he.seq hz, h32, h33, ?_, ?_⟩
  · intro i
    have h := hframe (retained i) (by dsimp [retained]; omega)
    rw [h]
    fin_cases i <;> rfl
  · have hp := prepareCost_bound a
    have hm := middle_bound a b ⟨t, ht, hr⟩
    have hf := finishCost_bound (middle a b) hm
    simp only [middle, prepared] at hf
    unfold localRuntimeBound
    omega

theorem result_scopes (a : Data) (b : SubexpLayoutConstruction.Data) :
    (result a b).stacks 45 = b.stacks 33 := by
  have h := finish_value workPorts exports (middle a b) (by decide)
    exports_separated (33, 45) (by simp [exports]) (by simp only [mem_workPorts]; decide)
  exact h.trans (embedState_stack id calleePort (prepared a) b calleePort_injective 33)

theorem result_tables (a : Data) (b : SubexpLayoutConstruction.Data) :
    (result a b).stacks 46 = b.stacks 32 := by
  have h := finish_value workPorts exports (middle a b) (by decide)
    exports_separated (32, 46) (by simp [exports]) (by simp only [mem_workPorts]; decide)
  exact h.trans (embedState_stack id calleePort (prepared a) b calleePort_injective 32)

theorem result_work (a : Data) (b : SubexpLayoutConstruction.Data) (i : Fin 48)
    (hi : i ∈ workPorts) : (result a b).stacks i = [] :=
  finish_empty workPorts exports (middle a b) i hi

theorem result_registers (a : Data) (b : SubexpLayoutConstruction.Data) (i : Fin 16) :
    (result a b).regs i = false := rfl

theorem result_input (a : Data) (b : SubexpLayoutConstruction.Data)
    (hi : ∀ i, b.stacks (retained i) = a.stacks ((retained i).castAdd 3)) (i : Fin 5) :
    (result a b).stacks ((retained i).castAdd 3) = a.stacks ((retained i).castAdd 3) := by
  change (finishState workPorts exports (middle a b)).stacks _ = _
  rw [finish_frame workPorts exports (middle a b) _ (by
    simp only [mem_workPorts, retained, Fin.val_castAdd]
    omega) (by
      intro q hq
      simp only [exports, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> intro he
      all_goals have hv := congrArg (fun j : Fin 48 => j.val) he
      all_goals simp only [retained, Fin.val_castAdd, Fin.coe_ofNat_eq_mod] at hv
      all_goals omega)]
  exact (embedState_stack id calleePort (prepared a) b calleePort_injective (retained i)).trans (hi i)

theorem result_temporary (a : Data) (b : SubexpLayoutConstruction.Data) :
    (result a b).stacks temporary = [] := by
  change (finishState workPorts exports (middle a b)).stacks temporary = []
  rw [finish_frame workPorts exports (middle a b) temporary (by
    simp only [mem_workPorts]; decide) (by
      intro q hq
      simp only [exports, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> decide)]
  unfold middle
  rw [embedState_stack_frame id calleePort (prepared a) b temporary (by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = 47 at hv
    omega)]
  exact prepare_temporary temporary workPorts [] a (by simp)

def inputIndex : Fin 5 → Fin 32 := ![2, 5, 6, 19, 9]

def highPort {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) : Fin 7 → Fin (totalStacks es) :=
  ![persistent es 2, persistent es 5, persistent es 6, persistent es 19,
    persistent es 9, SubexpLayoutPorts.scopes alloc, SubexpLayoutPorts.tables alloc]

theorem highPort_injective {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) :
    Function.Injective (highPort alloc) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hb := alloc.enough.trans alloc.within
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals norm_num [highPort, persistent, SubexpLayoutPorts.scopes,
    SubexpLayoutPorts.tables, SubexpLayoutPorts.master, SubexpLayoutPorts.ordinary] at hv <;> omega

theorem highPort_large {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) (i : Fin 7) :
    640 ≤ (highPort alloc i).val := by
  have hb := alloc.enough.trans alloc.within
  fin_cases i <;> norm_num [highPort, persistent, SubexpLayoutPorts.scopes,
    SubexpLayoutPorts.tables, SubexpLayoutPorts.master, SubexpLayoutPorts.ordinary] <;> omega

def baseMap {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) (i : Fin 48) :
    Fin (totalStacks es) :=
  if hi : 35 ≤ i.val ∧ i.val < 42 then highPort alloc ⟨i.val - 35, by omega⟩
  else SubexpLayoutPorts.ordinary alloc ⟨i.val, by omega⟩

theorem baseMap_injective {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) :
    Function.Injective (baseMap alloc) := by
  intro i j h
  by_cases hi : 35 ≤ i.val ∧ i.val < 42 <;> by_cases hj : 35 ≤ j.val ∧ j.val < 42
  · have he := highPort_injective alloc (by simpa only [baseMap, dite_eq_left hi, dite_eq_left hj] using h)
    have hv := congrArg Fin.val he
    apply Fin.ext
    dsimp only at hv
    omega
  · have hv := congrArg Fin.val h
    have hl := highPort_large alloc ⟨i.val - 35, by omega⟩
    simp only [baseMap, dite_eq_left hi, dite_eq_right hj, SubexpLayoutPorts.ordinary] at hv
    omega
  · have hv := congrArg Fin.val h
    have hl := highPort_large alloc ⟨j.val - 35, by omega⟩
    simp only [baseMap, dite_eq_right hi, dite_eq_left hj, SubexpLayoutPorts.ordinary] at hv
    omega
  · exact Fin.ext (congrArg (fun k : Fin (totalStacks es) => k.val)
      (by simpa only [baseMap, dite_eq_right hi, dite_eq_right hj] using h))

def permutation : Fin 48 ≃ Fin 48 := (Equiv.swap 40 45).trans (Equiv.swap 41 46)
def stackMap {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) (i : Fin 48) :=
  baseMap alloc (permutation i)

theorem stackMap_injective {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) :
    Function.Injective (stackMap alloc) := (baseMap_injective alloc).comp permutation.injective

@[simp] theorem stackMap_scopes {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) :
    stackMap alloc 45 = SubexpLayoutPorts.scopes alloc := rfl
@[simp] theorem stackMap_tables {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) :
    stackMap alloc 46 = SubexpLayoutPorts.tables alloc := rfl

@[simp] theorem stackMap_input {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) (i : Fin 5) :
    stackMap alloc ⟨35 + i.val, by omega⟩ = persistent es (inputIndex i) := by
  fin_cases i <;> rfl

def register (er : ℕ) : Fin 16 ↪ Fin (workRegs er) :=
  ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin (workRegs er) => k.val) h)⟩

def procedure (er : ℕ) {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) : Procedure er es where
  registers := 16
  stackCount := 48
  labels := size command + 1
  program := program
  register := register er
  stack := ⟨stackMap alloc, stackMap_injective alloc⟩

def sourceInputs {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) (a : MainState er es) :=
  inputs ((procedure er alloc).project a)

/-- Exact physical outputs and the frame needed by the next layout stage. -/
structure Result {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a b : MainState er es) (scopeRecords tableRecords : List (List Bool)) : Prop where
  scopes : b.stacks (SubexpLayoutPorts.scopes alloc) = Encoding.encodeList id scopeRecords
  tables : b.stacks (SubexpLayoutPorts.tables alloc) = Encoding.encodeList id tableRecords
  inputs : ∀ i, b.stacks (persistent es (inputIndex i)) = a.stacks (persistent es (inputIndex i))
  scratch : ∀ i ∈ workPorts, b.stacks (stackMap alloc i) = []
  temporary : b.stacks (stackMap alloc Factors.temporary) = []
  frame : ∀ j, (¬ ∃ i, stackMap alloc i = j) → b.stacks j = a.stacks j
  registers : ∀ i, b.regs ((procedure er alloc).registerMap i) = false
  registerFrame : ∀ j, (¬ ∃ i, (procedure er alloc).registerMap i = j) → b.regs j = a.regs j
  controls : ∀ i, b.regs (controlRegister er i) = a.regs (controlRegister er i)

theorem install_result {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (b : SubexpLayoutConstruction.Data)
    (scopeRecords tableRecords : List (List Bool))
    (hs : b.stacks 33 = Encoding.encodeList id scopeRecords)
    (ht : b.stacks 32 = Encoding.encodeList id tableRecords)
    (hi : ∀ i, b.stacks (retained i) = ((procedure er alloc).project a).stacks ((retained i).castAdd 3)) :
    Result alloc a ((procedure er alloc).install a (result ((procedure er alloc).project a) b))
      scopeRecords tableRecords := by
  let localStart := (procedure er alloc).project a
  have hp (i : Fin 48) := embedState_stack (procedure er alloc).registerMap
    (procedure er alloc).stack a (result localStart b) (procedure er alloc).stack.injective i
  constructor
  · exact (hp 45).trans ((result_scopes localStart b).trans hs)
  · exact (hp 46).trans ((result_tables localStart b).trans ht)
  · intro i
    have h := (hp ((retained i).castAdd 3)).trans (result_input localStart b hi i)
    change ((procedure er alloc).install a (result localStart b)).stacks
      (stackMap alloc ((retained i).castAdd 3)) =
      a.stacks (stackMap alloc ((retained i).castAdd 3)) at h
    have hm : stackMap alloc ((retained i).castAdd 3) = persistent es (inputIndex i) := by
      fin_cases i <;> rfl
    rw [hm] at h
    exact h
  · intro i hi
    exact (hp i).trans (result_work localStart b i hi)
  · exact (hp temporary).trans (result_temporary localStart b)
  · intro j hj
    exact embedState_stack_frame _ _ _ _ _ hj
  · intro i
    exact (embedState_register _ _ _ _ (procedure er alloc).registerMap_injective i).trans
      (result_registers localStart b i)
  · intro j hj
    exact embedState_register_frame _ _ _ _ _ hj
  · exact Procedure.install_control _ _ _

def runtimeBound {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) (a : MainState er es)
    (hv : SubexpClauseFamilyProgram.Valid (SubexpLayoutConstruction.familyInputs (sourceInputs alloc a))
      (SubexpLayoutConstruction.dimension (sourceInputs alloc a))
      (SubexpLayoutConstruction.variableCount (sourceInputs alloc a)))
    (clauses : List (List (SAT.Literal (Fin (SubexpLayoutConstruction.variableCount (sourceInputs alloc a)))))) : ℕ :=
  localRuntimeBound ((procedure er alloc).project a) hv clauses + 1

/-- This theorem invokes both concrete factor producers. Its premises identify
the actual retained scalar and clause words, rather than supplying factor
streams or a semantic preprocessing function. -/
theorem execution {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) (a : MainState er es)
    (hell : 0 < CounterPrograms.value (sourceInputs alloc a).counts.ell)
    (hwidth : CounterPrograms.value (sourceInputs alloc a).counts.ell ≤
      (sourceInputs alloc a).counts.modulus.length)
    (hv : SubexpClauseFamilyProgram.Valid (SubexpLayoutConstruction.familyInputs (sourceInputs alloc a))
      (SubexpLayoutConstruction.dimension (sourceInputs alloc a))
      (SubexpLayoutConstruction.variableCount (sourceInputs alloc a)))
    (clauses : List (List (SAT.Literal (Fin (SubexpLayoutConstruction.variableCount (sourceInputs alloc a))))))
    (hsource : (sourceInputs alloc a).leaf = Encoding.encodeList SubexpClauseRowProgram.clauseBytes clauses) :
    ∃ n ≤ runtimeBound alloc a hv clauses, ∃ b,
      Eval (procedure er alloc).invoke n a b ∧
      Result alloc a b (SubexpLayoutConstruction.scopes (sourceInputs alloc a) clauses)
        (SubexpLayoutConstruction.tables (sourceInputs alloc a) hv clauses) := by
  obtain ⟨out, n, he, ht, hs, hi, hn⟩ :=
    local_execution ((procedure er alloc).project a) hell hwidth hv clauses hsource
  refine ⟨n + 1, Nat.add_le_add_right hn 1,
    (procedure er alloc).install a (result ((procedure er alloc).project a) out), ?_, ?_⟩
  · exact Procedure.invoke_trace _ _ _ (compiled_halt_trace he 39 45)
  · exact install_result alloc a out _ _ hs ht hi

end Factors
end SubexponentialSAT.SubexpMainLayout

end OAI.Algorithms
