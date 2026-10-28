import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupBoundSpec

namespace OAI.Algorithms

/-! Physical isolated calls in the coefficient adapter's fixed 64-stack bank. -/

namespace SubexponentialSAT.SubexpCoefficientStaging

open BitProgram StructuredCalls SubexpSetupStorage SubexpSetupBoundSpec

abbrev Data := State 16 64
abbrev Code := Cmd 16 64

structure Stage where
  registers : ℕ
  stackCount : ℕ
  labels : ℕ
  program : Program registers stackCount labels
  register_le : registers ≤ 16
  stack_le : stackCount ≤ 32
  inputs : List (Fin 64 × Fin 64)
  inputs_length : inputs.length ≤ 3
  inputs_nodup : (inputs.map Prod.snd).Nodup
  source_high : ∀ p ∈ inputs, 32 ≤ p.1.val ∧ p.1.val < 63
  target_low : ∀ p ∈ inputs, p.2.val < stackCount
  output : Fin stackCount
  destination : Fin 64
  destination_high : 32 ≤ destination.val ∧ destination.val < 63

namespace Stage

def register (s : Stage) (i : Fin s.registers) : Fin 16 := i.castLE s.register_le
def stack (s : Stage) (i : Fin s.stackCount) : Fin 64 :=
  i.castLE (s.stack_le.trans (by decide))
def work (s : Stage) : List (Fin 64) := List.ofFn s.stack
def outputs (s : Stage) : List (Fin 64 × Fin 64) := [(s.stack s.output, s.destination)]
def prepared (s : Stage) (a : Data) : Data := prepareState 63 s.work s.inputs a
noncomputable def middle (s : Stage) (a : Data) (out : State s.registers s.stackCount) : Data :=
  embedState s.register s.stack (s.prepared a) out
noncomputable def result (s : Stage) (a : Data) (out : State s.registers s.stackCount) : Data :=
  finishState s.work s.outputs (s.middle a out)
def command (s : Stage) : Code :=
  isolated s.program s.register s.stack 63 s.work s.inputs s.outputs

theorem register_injective (s : Stage) : Function.Injective s.register := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 16 => x.val) h)

theorem stack_injective (s : Stage) : Function.Injective s.stack := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 64 => x.val) h)

@[simp] theorem mem_work (s : Stage) (i : Fin 64) : i ∈ s.work ↔ i.val < s.stackCount := by
  simp only [work, List.mem_ofFn]
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

theorem stack_low (s : Stage) (i : Fin s.stackCount) : (s.stack i).val < 32 :=
  i.isLt.trans_le s.stack_le

theorem inputs_good (s : Stage) : ∀ p ∈ s.inputs,
    p.1 ≠ p.2 ∧ p.1 ≠ 63 ∧ (63 : Fin 64) ≠ p.2 := by
  intro p hp
  have hh := s.source_high p hp
  have hl := (s.target_low p hp).trans_le s.stack_le
  refine ⟨?_, ?_, ?_⟩ <;> intro h
  all_goals have hv := congrArg (fun x : Fin 64 => x.val) h
  all_goals norm_num at hv
  all_goals omega

theorem inputs_separated (s : Stage) : ∀ p ∈ s.inputs, ∀ q ∈ s.inputs, p.1 ≠ q.2 := by
  intro p hp q hq h
  have hh := s.source_high p hp
  have hl := (s.target_low q hq).trans_le s.stack_le
  have hv := congrArg (fun x : Fin 64 => x.val) h
  omega

theorem outputs_good (s : Stage) : ∀ p ∈ s.outputs,
    p.1 ≠ p.2 ∧ p.1 ≠ 63 ∧ (63 : Fin 64) ≠ p.2 := by
  intro p hp
  obtain rfl := List.mem_singleton.mp hp
  have hl := s.stack_low s.output
  have hh := s.destination_high
  refine ⟨?_, ?_, ?_⟩ <;> intro h
  all_goals have hv := congrArg (fun x : Fin 64 => x.val) h
  all_goals norm_num at hv
  all_goals omega

theorem outputs_separated (s : Stage) : ∀ p ∈ s.outputs, ∀ q ∈ s.outputs, p.1 ≠ q.2 := by
  intro p hp q hq
  obtain rfl := List.mem_singleton.mp hp
  obtain rfl := List.mem_singleton.mp hq
  exact (s.outputs_good _ (List.mem_singleton_self _)).1

theorem temporary_frame (s : Stage) : ¬ ∃ j, s.stack j = 63 := by
  rintro ⟨j, hj⟩
  have hl := s.stack_low j
  have hv := congrArg (fun x : Fin 64 => x.val) hj
  norm_num at hv
  omega

theorem destination_not_work (s : Stage) : s.destination ∉ s.work := by
  rw [mem_work]
  have := s.destination_high
  have := s.stack_le
  omega

theorem result_output (s : Stage) (a : Data) (out : State s.registers s.stackCount) :
    (s.result a out).stacks s.destination = out.stacks s.output := by
  have h := finish_value s.work s.outputs (s.middle a out)
    (by simp [outputs]) s.outputs_separated (s.stack s.output, s.destination)
    (List.mem_singleton_self _) s.destination_not_work
  exact h.trans (embedState_stack s.register s.stack (s.prepared a) out s.stack_injective s.output)

theorem result_frame (s : Stage) (a : Data) (out : State s.registers s.stackCount)
    (i : Fin 64) (hi : 32 ≤ i.val) (ht : i ≠ 63) (hd : i ≠ s.destination) :
    (s.result a out).stacks i = a.stacks i := by
  have hw : i ∉ s.work := by rw [mem_work]; have := s.stack_le; omega
  unfold result
  rw [finish_frame s.work s.outputs (s.middle a out) i hw (by simpa [outputs] using hd)]
  unfold middle
  rw [embedState_stack_frame s.register s.stack (s.prepared a) out i (by
    rintro ⟨j, hj⟩
    have hl := s.stack_low j
    have hv := congrArg (fun x : Fin 64 => x.val) hj
    omega)]
  apply prepare_frame 63 s.work s.inputs a i ht hw
  intro p hp he
  have hl := (s.target_low p hp).trans_le s.stack_le
  have hv := congrArg (fun x : Fin 64 => x.val) he
  omega

theorem run (s : Stage) (a : Data) (out : State s.registers s.stackCount)
    (B T : ℕ) (ha : WordBound B a)
    (hrun : RunsIn s.program T
      ((project s.register s.stack (s.prepared a)).withPC (some s.program.entry))
      (out.withPC none)) :
    ∃ t, Eval s.command t a (s.result a out) ∧
      t ≤ 400 * (B + T + 1) ∧ WordBound (B + T) (s.result a out) := by
  obtain ⟨t, ht, he⟩ := hrun
  have hp : WordBound B (s.prepared a) :=
    prepare_wordBound 63 s.work s.inputs a B s.inputs_nodup
      (fun p hp => (s.mem_work p.2).mpr (s.target_low p hp)) s.inputs_separated ha
  have hcall := invoke_eval s.program s.register s.stack s.register_injective
    s.stack_injective (s.prepared a) out he
  have hm : WordBound (B + T) (s.middle a out) :=
    wordBound_mono (eval_wordBound hp hcall) (Nat.add_le_add_left ht B)
  have hf : WordBound (B + T) (s.result a out) :=
    finish_wordBound s.work s.outputs (s.middle a out) (B + T)
      (by simp [outputs]) s.outputs_separated hm
  have hpc := prepareCost_le 63 s.work s.inputs a B s.inputs_separated ha
  have hfc := finishCost_le s.work s.outputs (s.middle a out) (B + T)
    (by simp [outputs]) s.outputs_separated hm
  have hw : s.work.length = s.stackCount := by simp [work]
  have ho : s.outputs.length = 1 := rfl
  rw [hw] at hpc hfc
  rw [ho] at hfc
  have hsc := s.stack_le
  have hic := s.inputs_length
  have hc1 := Nat.mul_le_mul_right (2 * B + 3) hsc
  have hc2 := Nat.mul_le_mul_right (7 * B + 5) hic
  have hc3 := Nat.mul_le_mul_right (2 * (B + T) + 3) hsc
  refine ⟨prepareCost 63 s.work s.inputs a +
    (t + finishCost s.work s.outputs (s.middle a out)), ?_, ?_, hf⟩
  · exact isolated_eval s.program s.register s.stack s.register_injective
      s.stack_injective 63 s.work s.inputs s.outputs a out s.inputs_good
      s.outputs_good s.temporary_frame he
  · omega

end Stage
end SubexponentialSAT.SubexpCoefficientStaging

end OAI.Algorithms
