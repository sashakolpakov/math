import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BankRoutines
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms

namespace OAI.Algorithms

/-!
# Preparing the quartic test bank from the prime word

The prime word supplies the runtime width. Fourteen copies initialize the
scalar bank, and a genuine binary decrement turns word six into p minus one.
This initialization needs no polynomial coefficients.
-/

namespace SubexponentialSAT.SubexpQuarticBootstrap

open BitProgram StructuredCalls StackRoutines

def bankPort (i : Fin 14) : Fin 35 := Fin.castAdd 21 i
def bankPorts : List (Fin 35) := List.ofFn bankPort

def decrementPorts : CounterForPrograms.Ports 14 35 where
  register := ⟨![0, 1, 2], by decide⟩
  counter := 6
  scratch := 22
  counter_ne_scratch := by decide

abbrev command : Cmd 14 35 :=
  .seq (BankRoutines.fillCmd 31 22 0 1 bankPorts)
    (CounterForPrograms.decrementCmd decrementPorts)

@[simp] theorem bankPorts_length : bankPorts.length = 14 := by simp [bankPorts]
theorem bankPorts_nodup : bankPorts.Nodup := by decide
theorem bankPort_mem (i : Fin 14) : bankPort i ∈ bankPorts := by
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem six_mem : (6 : Fin 35) ∈ bankPorts := by decide
theorem temporary_not_mem : (22 : Fin 35) ∉ bankPorts := by decide
theorem shape_not_mem : (31 : Fin 35) ∉ bankPorts := by decide

theorem command_eval (d : State 14 35) (primeWord : List Bool)
    (hshape : d.stacks 31 = primeWord)
    (hempty : ∀ j ∈ bankPorts, d.stacks j = [])
    (htemporary : d.stacks 22 = [])
    (hpositive : 0 < CounterPrograms.value primeWord) :
    ∃ n next,
      n ≤ 110 * (primeWord.length + 1) ∧ Eval command n d next ∧
      next.stacks 6 = CounterPrograms.ripple false primeWord ∧
      next.stacks 22 = [] ∧
      (∀ i : Fin 14, (next.stacks (bankPort i)).length = primeWord.length) ∧
      (∀ j : Fin 35, j ∉ bankPorts → next.stacks j = d.stacks j) ∧
      (∀ j : Fin 14, j ≠ 0 → j ≠ 1 → j ≠ 2 → next.regs j = d.regs j) := by
  let filled : State 14 35 :=
    ⟨readRegs d.regs 0 1 none, BankRoutines.fillStacks 31 bankPorts d.stacks⟩
  let next := CounterForPrograms.decrementResult decrementPorts filled
  have hfill := BankRoutines.fill_eval 31 22 0 1 bankPorts bankPorts_nodup
    shape_not_mem temporary_not_mem (by decide) (by decide) d.regs d.stacks
    hempty htemporary
  have hsix : filled.stacks 6 = primeWord := by
    simpa [filled, hshape] using
      BankRoutines.fillStacks_mem 31 (6 : Fin 35) bankPorts d.stacks six_mem
  have htemp : filled.stacks 22 = [] := by
    simpa [filled, htemporary] using
      BankRoutines.fillStacks_frame 31 (22 : Fin 35) bankPorts d.stacks temporary_not_mem
  have hdec := CounterForPrograms.decrement_eval decrementPorts filled htemp
  rw [show filled.stacks decrementPorts.counter = primeWord from hsix] at hdec
  have hresult : next.stacks 6 = CounterPrograms.ripple false primeWord := by
    simpa only [next, decrementPorts, hsix] using
      CounterForPrograms.decrementResult_counter decrementPorts filled
  refine ⟨14 * (7 * primeWord.length + 5) + 3 +
      (CounterPrograms.rippleCost false primeWord + 1), next, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc := CounterPrograms.rippleCost_le false primeWord
    omega
  · simpa only [command, bankPorts_length, hshape, hsix] using hfill.seq hdec
  · exact hresult
  · exact CounterForPrograms.decrementResult_scratch decrementPorts filled
  · intro i
    by_cases hi : bankPort i = (6 : Fin 35)
    · rw [hi, hresult, CounterPrograms.decrement_length hpositive]
    · have hit : bankPort i ≠ (22 : Fin 35) := by
        intro h
        exact temporary_not_mem (h ▸ bankPort_mem i)
      have hf := CounterForPrograms.install_other_stack decrementPorts filled
        false false (filled.regs (decrementPorts.register 2))
        (CounterPrograms.ripple false (filled.stacks 6)) [] (bankPort i) hi hit
      change next.stacks (bankPort i) = filled.stacks (bankPort i) at hf
      rw [hf]
      simpa [filled, hshape] using congrArg List.length
        (BankRoutines.fillStacks_mem 31 (bankPort i) bankPorts d.stacks (bankPort_mem i))
  · intro j hj
    by_cases ht : j = (22 : Fin 35)
    · subst j
      rw [show next.stacks 22 = [] from
        CounterForPrograms.decrementResult_scratch decrementPorts filled, htemporary]
    · have h6 : j ≠ (6 : Fin 35) := by
        intro h
        apply hj
        simpa only [h] using six_mem
      have hf := CounterForPrograms.install_other_stack decrementPorts filled
        false false (filled.regs (decrementPorts.register 2))
        (CounterPrograms.ripple false (filled.stacks 6)) [] j h6 ht
      change next.stacks j = filled.stacks j at hf
      exact hf.trans (BankRoutines.fillStacks_frame 31 j bankPorts d.stacks hj)
  · intro j h0 h1 h2
    have hf : next.regs j = filled.regs j := by
      apply StructuredCalls.embedState_register_frame
      rintro ⟨i, hi⟩
      fin_cases i <;> simp_all [decrementPorts]
    exact hf.trans (readRegs_frame d.regs 0 1 j none h0 h1)

/-- The physical constant has exactly the value needed by the scalar tests. -/
theorem decremented_value (primeWord : List Bool) (p : ℕ)
    (hp : 0 < p) (hv : BinaryArithmetic.toNat primeWord = p) :
    BinaryArithmetic.toNat (CounterPrograms.ripple false primeWord) = p - 1 := by
  have hp' : 0 < CounterPrograms.value primeWord := by
    simpa only [CounterPrograms.value_eq_toNat, hv] using hp
  have h := CounterPrograms.value_decrement hp'
  simp only [CounterPrograms.value_eq_toNat, hv] at h
  omega

end SubexponentialSAT.SubexpQuarticBootstrap

end OAI.Algorithms
