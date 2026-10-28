import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainPackingStagingCore
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgram

namespace OAI.Algorithms

/-! Actual fixed packing invocation between the physical staging operations.
The Main endpoint supplies the producer's proved execution to this internal
trace-composition lemma. -/

namespace SubexponentialSAT.SubexpMainPacking.Staging

open BitProgram StructuredCalls SubexpSetupStorage Subexp

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev command : Cmd 16 61 := .seq
  (isolated PackingProgram.program id calleePort temporary workPorts copies exports)
  RegisterResetProgram.all

def program := compiled command 48 54

theorem middle_bound (a : Data) (b : PackingProgramSupport.Data) {T : ℕ}
    (hrun : RunsIn PackingProgram.program T
      ((project id calleePort (prepared a)).withPC (some PackingProgram.program.entry))
      (b.withPC none)) :
    SubexpPreparedSetupCalls.StackBound (middle a b) (48 * stackBits a.stacks + T) := by
  have hi (i : Fin 48) : ((project id calleePort (prepared a)).stacks i).length ≤ stackBits a.stacks :=
    prepared_bound a (calleePort i)
  have his : stackBits (project id calleePort (prepared a)).stacks ≤ 48 * stackBits a.stacks := by
    have h := Finset.sum_le_sum (fun (i : Fin 48) (_ : i ∈ Finset.univ) => hi i)
    unfold stackBits
    calc
      _ ≤ ∑ _i : Fin 48, stackBits a.stacks := h
      _ = 48 * stackBits a.stacks := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
  have hg := runsIn_dataBits PackingProgram.program hrun
  change stackBits b.stacks ≤ stackBits (project id calleePort (prepared a)).stacks + T at hg
  intro i
  by_cases hm : ∃ j, calleePort j = i
  · obtain ⟨j, rfl⟩ := hm
    have hj : (b.stacks j).length ≤ stackBits b.stacks :=
      Finset.single_le_sum (fun (k : Fin 48) _ => Nat.zero_le (b.stacks k).length) (Finset.mem_univ j)
    unfold middle
    rw [embedState_stack id calleePort _ b calleePort_injective]
    omega
  · unfold middle
    rw [embedState_stack_frame id calleePort _ b i hm]
    have h := prepared_bound a i
    omega

/-- Internal composition of real copies and cleanup with a real producer
trace. The public Main theorem supplies that trace from PackingExecution. -/
theorem run_of_trace (a : Data) (b : PackingProgramSupport.Data) {t T : ℕ} (ht : t ≤ T)
    (hrun : Trace PackingProgram.program t
      ((PackingProgram.inputState (inputs a) (prepared a).regs).withPC (some PackingProgram.program.entry))
      (b.withPC none)) :
    RunsIn program (runtimeBound a T)
      (a.withPC (some program.entry)) ((result a b).withPC none) := by
  have hr : Trace PackingProgram.program t
      ((project id calleePort (prepared a)).withPC (some PackingProgram.program.entry))
      (b.withPC none) := by simpa only [prepared_entry] using hrun
  have he := isolated_eval PackingProgram.program id calleePort Function.injective_id
    calleePort_injective temporary workPorts copies exports a b copies_good exports_good (by
      rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      change i.val = 60 at hv
      omega) hr
  have hz := RegisterResetProgram.all_eval (finishState workPorts exports (middle a b))
  refine ⟨_, ?_, compiled_halt_trace (he.seq hz) 48 54⟩
  have hp := prepareCost_bound a
  have hm := middle_bound a b ⟨t, ht, hr⟩
  have hf := finishCost_bound (middle a b) hm
  dsimp only [middle, prepared] at hf
  unfold runtimeBound
  omega

end SubexponentialSAT.SubexpMainPacking.Staging

end OAI.Algorithms
