import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgramInput
import OAI.Algorithms.SubexponentialSAT.SubexpMainPackingPorts
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedSetupBounds
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

namespace OAI.Algorithms

/-! Physical input/output storage, frames and charged copy/clear overhead
for the Main packing adapter. The concrete producer call is composed in
SubexpMainPackingStaging. -/

namespace SubexponentialSAT.SubexpMainPacking.Staging

open BitProgram StructuredCalls SubexpSetupStorage Subexp

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 16 61

def inputTarget (i : Fin 6) : Fin 48 := ⟨40 + i.val, by omega⟩
def outputSource (i : Fin 6) : Fin 48 := ⟨30 + i.val, by omega⟩
def workPorts : List (Fin 61) := (List.finRange 61).filter (fun i => decide (i.val < 48))
def copies : List (Fin 61 × Fin 61) := List.ofFn (fun i => (inputPort i, calleePort (inputTarget i)))
def exports : List (Fin 61 × Fin 61) := List.ofFn (fun i => (calleePort (outputSource i), outputPort i))

@[simp] theorem mem_workPorts (i : Fin 61) : i ∈ workPorts ↔ i.val < 48 := by
  simp [workPorts]

theorem input_not_work (i : Fin 6) : inputPort i ∉ workPorts := by
  simp [inputPort]

theorem input_ne_temporary (i : Fin 6) : inputPort i ≠ temporary := by
  intro h
  have hv := congrArg Fin.val h
  change 48 + i.val = 60 at hv
  omega

theorem copies_good : ∀ q ∈ copies,
    q.1 ≠ q.2 ∧ q.1 ≠ temporary ∧ temporary ≠ q.2 := by
  intro q hq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  refine ⟨?_, input_ne_temporary i, ?_⟩ <;> intro h <;>
    have hv := congrArg Fin.val h
  · change 48 + i.val = 40 + i.val at hv
    omega
  · change 60 = 40 + i.val at hv
    omega

theorem exports_good : ∀ q ∈ exports,
    q.1 ≠ q.2 ∧ q.1 ≠ temporary ∧ temporary ≠ q.2 := by
  intro q hq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> have hv := congrArg Fin.val h
  · change 30 + i.val = 54 + i.val at hv
    omega
  · change 30 + i.val = 60 at hv
    omega
  · change 60 = 54 + i.val at hv
    omega

theorem copies_separated : ∀ q ∈ copies, ∀ z ∈ copies, q.1 ≠ z.2 := by
  intro q hq z hz he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  have hv := congrArg Fin.val he
  change 48 + i.val = 40 + j.val at hv
  omega

theorem exports_separated : ∀ q ∈ exports, ∀ z ∈ exports, q.1 ≠ z.2 := by
  intro q hq z hz he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  have hv := congrArg Fin.val he
  change 30 + i.val = 54 + j.val at hv
  omega

def inputs (a : Data) : PackingProgram.Input :=
  ⟨a.stacks 48, a.stacks 49, a.stacks 50, a.stacks 51, a.stacks 52, a.stacks 53⟩

def prepared (a : Data) : Data := prepareState temporary workPorts copies a

theorem cleared_targets (a : Data) :
    ∀ q ∈ copies, (beforeCopies temporary workPorts a).stacks q.2 = [] := by
  intro q hq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  simp [beforeCopies, resetMany_stacks, clearMany_stacks,
    calleePort, inputTarget, show 40 + i.val < 48 by omega]

theorem prepared_input (a : Data) (i : Fin 6) :
    (prepared a).stacks (calleePort (inputTarget i)) = a.stacks (inputPort i) := by
  have h := copyMany_value copies (beforeCopies temporary workPorts a)
    (by decide) (cleared_targets a) copies_separated
    (inputPort i, calleePort (inputTarget i)) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hf : (beforeCopies temporary workPorts a).stacks (inputPort i) = a.stacks (inputPort i) := by
    simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
      ite_eq_right (input_not_work i), List.mem_singleton, ite_eq_right (input_ne_temporary i)]
  exact h.trans hf

theorem prepared_other (a : Data) (i : Fin 48) (hi : ∀ j, inputTarget j ≠ i) :
    (prepared a).stacks (calleePort i) = [] := by
  have h := copyMany_frame copies (beforeCopies temporary workPorts a) (calleePort i) (by
    intro q hq he
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact hi j (calleePort_injective he).symm)
  rw [show prepared a = copyManyState copies (beforeCopies temporary workPorts a) from rfl, h]
  simp [beforeCopies, resetMany_stacks, clearMany_stacks, calleePort, i.isLt]

theorem inputState_target (a : Data) (regs : Fin 16 → Bool) (i : Fin 6) :
    (PackingProgram.inputState (inputs a) regs).stacks (inputTarget i) = a.stacks (inputPort i) := by
  fin_cases i <;> rfl

theorem prepared_entry (a : Data) :
    project id calleePort (prepared a) = PackingProgram.inputState (inputs a) (prepared a).regs := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    change (prepared a).stacks (calleePort i) = (PackingProgram.inputState (inputs a) (prepared a).regs).stacks i
    by_cases hm : 40 ≤ i.val ∧ i.val < 46
    · let j : Fin 6 := ⟨i.val - 40, by omega⟩
      have hi : i = inputTarget j := by
        apply Fin.ext
        dsimp [inputTarget, j]
        omega
      rw [hi, prepared_input, inputState_target]
    · rw [prepared_other a i (by
        intro j he
        have hv := congrArg Fin.val he
        change 40 + j.val = i.val at hv
        omega)]
      simp only [PackingProgram.inputState]
      split_ifs <;> first | rfl | omega

noncomputable def middle (a : Data) (b : PackingProgramSupport.Data) : Data :=
  embedState id calleePort (prepared a) b

noncomputable def result (a : Data) (b : PackingProgramSupport.Data) : Data :=
  RegisterResetProgram.zeroed (finishState workPorts exports (middle a b))

theorem result_output (a : Data) (b : PackingProgramSupport.Data) (i : Fin 6) :
    (result a b).stacks (outputPort i) = b.stacks (outputSource i) := by
  have h := finish_value workPorts exports (middle a b) (by decide) exports_separated
    (calleePort (outputSource i), outputPort i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
    (by rw [mem_workPorts]; dsimp [outputPort]; omega)
  exact h.trans (embedState_stack id calleePort (prepared a) b calleePort_injective (outputSource i))

theorem result_input (a : Data) (b : PackingProgramSupport.Data) (i : Fin 6) :
    (result a b).stacks (inputPort i) = a.stacks (inputPort i) := by
  change (finishState workPorts exports (middle a b)).stacks _ = _
  rw [finish_frame workPorts exports (middle a b) _ (input_not_work i) (by
    intro q hq he
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    have hv := congrArg Fin.val he
    change 48 + i.val = 54 + j.val at hv
    omega)]
  unfold middle
  rw [embedState_stack_frame id calleePort (prepared a) b _ (by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = 48 + i.val at hv
    omega)]
  apply prepare_frame _ _ _ _ _ (input_ne_temporary i) (input_not_work i)
  intro q hq he
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
  have hv := congrArg Fin.val he
  change 48 + i.val = 40 + j.val at hv
  omega

theorem result_work (a : Data) (b : PackingProgramSupport.Data) (i : Fin 48) :
    (result a b).stacks (calleePort i) = [] :=
  finish_empty workPorts exports (middle a b) (calleePort i) (by simp [calleePort])

theorem result_temporary (a : Data) (b : PackingProgramSupport.Data) :
    (result a b).stacks temporary = [] := by
  change (finishState workPorts exports (middle a b)).stacks temporary = []
  rw [finish_frame workPorts exports (middle a b) temporary (by simp [temporary]) (by
    intro q hq he
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    have hv := congrArg Fin.val he
    change 60 = 54 + j.val at hv
    omega)]
  unfold middle
  rw [embedState_stack_frame id calleePort (prepared a) b temporary (by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = 60 at hv
    omega)]
  exact prepare_temporary temporary workPorts copies a copies_good

theorem result_registers (a : Data) (b : PackingProgramSupport.Data) (i : Fin 16) :
    (result a b).regs i = false := rfl

theorem data_bound (a : Data) :
    SubexpPreparedSetupCalls.StackBound a (stackBits a.stacks) := by
  intro i
  exact Finset.single_le_sum (fun (j : Fin 61) _ => Nat.zero_le (a.stacks j).length) (Finset.mem_univ i)

theorem prepared_bound (a : Data) :
    SubexpPreparedSetupCalls.StackBound (prepared a) (stackBits a.stacks) := by
  apply SubexpPreparedSetupCalls.copyMany_bound _ _
    (SubexpPreparedSetupCalls.beforeCopies_bound temporary workPorts a (data_bound a))
    (by decide) (cleared_targets a) copies_separated

theorem prepareCost_bound (a : Data) :
    prepareCost temporary workPorts copies a ≤ 500 * (stackBits a.stacks + 1) := by
  have h1 := SubexpPreparedSetupCalls.clearManyCost_le [temporary] a (data_bound a)
  have h2 := SubexpPreparedSetupCalls.clearManyCost_le workPorts (clearManyState [temporary] a)
    (SubexpPreparedSetupCalls.clearMany_bound [temporary] a (data_bound a))
  have h3 := SubexpPreparedSetupCalls.copyManyCost_le copies (beforeCopies temporary workPorts a)
    (fun q _ => SubexpPreparedSetupCalls.beforeCopies_bound temporary workPorts a (data_bound a) q.1)
    copies_separated
  have hw : workPorts.length = 48 := by decide
  have hc : copies.length = 6 := List.length_ofFn
  rw [hw] at h2
  rw [hc] at h3
  simp only [List.length_singleton, one_mul] at h1
  unfold prepareCost
  omega

theorem finishCost_bound (a : Data) {W : ℕ}
    (ha : SubexpPreparedSetupCalls.StackBound a W) :
    finishCost workPorts exports a ≤ 500 * (W + 1) := by
  let b := clearManyState (exports.map Prod.snd) a
  have hb := SubexpPreparedSetupCalls.clearMany_bound (exports.map Prod.snd) a ha
  have hc : SubexpPreparedSetupCalls.StackBound (copyManyState exports b) W := by
    apply SubexpPreparedSetupCalls.copyMany_bound _ _ hb (by decide) ?_ exports_separated
    intro q hq
    exact (clearMany_stacks _ a q.2).trans (ite_eq_left (List.mem_map.mpr ⟨q, hq, rfl⟩))
  have h1 := SubexpPreparedSetupCalls.clearManyCost_le (exports.map Prod.snd) a ha
  have h2 := SubexpPreparedSetupCalls.copyManyCost_le exports b (fun q _ => hb q.1) exports_separated
  have h3 := SubexpPreparedSetupCalls.clearManyCost_le workPorts (copyManyState exports b) hc
  have he : exports.length = 6 := List.length_ofFn
  have hw : workPorts.length = 48 := by decide
  rw [List.length_map, he] at h1
  rw [he] at h2
  rw [hw] at h3
  change clearManyCost (exports.map Prod.snd) a +
    (copyManyCost exports b + (clearManyCost workPorts (copyManyState exports b) + 9)) ≤ _
  omega

def runtimeBound (a : Data) (T : ℕ) : ℕ := 30000 * (stackBits a.stacks + T + 1)

end SubexponentialSAT.SubexpMainPacking.Staging

end OAI.Algorithms
