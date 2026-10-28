import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram
import OAI.Algorithms.SubexponentialSAT.BinaryPrograms
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

/-! A fixed finite binary accumulator with actual source traces and local prefixSteps bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.Accumulator

open BitProgram StructuredCalls

def registers : Fin 3 ↪ Fin 8 where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)

def state (regs : Fin 8 → Bool) (left right : List Bool) : StructuredProgram.State 8 3 :=
  ⟨regs, BinaryPrograms.Add.stackState left right []⟩

/-- One fixed bit program adds and immediately canonicalizes the accumulator.
The output occupies stack zero; both temporary stacks are empty at return. -/
def command : Cmd 8 3 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.call BinaryPrograms.Add.littleEndianProgram)
      (.call (ProgramLinking.liftProgram CanonicalWordProgram.normalizeUnsignedProgram
        registers id)))

theorem command_eval (regs : Fin 8 → Bool) (left right : List Bool) :
    ∃ t final,
      t ≤ 33 * (max left.length right.length + 1) + 30 ∧
      Eval command t (state regs left right) final ∧
      final.stacks 0 = binaryNat (CounterPrograms.value left + CounterPrograms.value right) ∧
      final.stacks 1 = [] ∧ final.stacks 2 = [] := by
  let regs₀ := Function.update regs 0 false
  let word := BinaryArithmetic.add left right
  obtain ⟨rf, ta, hta, htrace⟩ := BinaryPrograms.Add.littleEndian_run regs₀ left right
  let middle := state rf word []
  have hadd : Eval (.call BinaryPrograms.Add.littleEndianProgram) ta
      (state regs₀ left right) middle := by
    apply Eval.call
    simpa only [state, middle, regs₀, word, BinaryArithmetic.add,
      StructuredProgram.State.withPC, Function.update_self,
      show BinaryPrograms.Add.littleEndianProgram.entry = 0 by rfl] using htrace
  obtain ⟨tn, htn, hnormal⟩ := CanonicalWordProgram.normalizeUnsigned_call registers
    (Function.Embedding.refl (Fin 3)) middle (rf ∘ registers) word
  have hstart : embedState registers id middle
      (CanonicalWordProgram.state (rf ∘ registers) word []) = middle := by
    apply embedState_eq_of_ports registers id middle middle _ registers.injective
      Function.injective_id
    · intro i
      rfl
    · intro i hi
      rfl
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      exact (hi ⟨i, rfl⟩).elim
  change Eval (.call (ProgramLinking.liftProgram CanonicalWordProgram.normalizeUnsignedProgram
    registers id)) tn (embedState registers id middle
      (CanonicalWordProgram.state (rf ∘ registers) word []))
    (embedState registers id middle
      (CanonicalWordProgram.state CanonicalWordProgram.zeroRegs
        (binaryNat (CounterPrograms.value word)) [])) at hnormal
  rw [hstart] at hnormal
  have hreset : Eval (.base (.atom (.set (0 : Fin 8) false))) 1
      (state regs left right) (state regs₀ left right) :=
    .base (.atom _ _)
  have hlength := BinaryArithmetic.length_add left right
  refine ⟨1 + (ta + tn), _, ?_, hreset.seq (hadd.seq hnormal), ?_, ?_, ?_⟩
  · dsimp [word] at htn
    omega
  · calc
      _ = binaryNat (CounterPrograms.value word) :=
        embedState_stack registers id _ _ Function.injective_id (0 : Fin 3)
      _ = _ := by
        simp only [word, CounterPrograms.value_eq_toNat, BinaryArithmetic.toNat_add]
  · exact embedState_stack registers id _ _ Function.injective_id (1 : Fin 3)
  · exact embedState_stack registers id _ _ Function.injective_id (2 : Fin 3)

def program : Program 8 3 (StructuredCalls.size command + 1) :=
  StructuredCalls.compiled command 0 0

theorem program_runs (regs : Fin 8 → Bool) (left right : List Bool) :
    ∃ final : StructuredProgram.State 8 3,
      RunsIn program (33 * (max left.length right.length + 1) + 31)
        ((state regs left right).withPC (some program.entry)) (final.withPC none) ∧
      final.stacks 0 = binaryNat (CounterPrograms.value left + CounterPrograms.value right) ∧
      final.stacks 1 = [] ∧ final.stacks 2 = [] := by
  obtain ⟨t, final, ht, he, houtput, h1, h2⟩ := command_eval regs left right
  exact ⟨final, ⟨t + 1, by omega, compiled_halt_trace he 0 0⟩, houtput, h1, h2⟩

/-- The runtime bound is linear in both input word lengths, so this local
trace-growth estimate is polynomial independently of the number of leaves. -/
theorem prefix_dataBits_le (regs : Fin 8 → Bool) (left right : List Bool)
    (prefixSteps : ℕ) (c : Cfg 8 3 (StructuredCalls.size command + 1))
    (hp : prefixSteps ≤ 33 * (max left.length right.length + 1) + 31)
    (htrace : Trace program prefixSteps
      ((state regs left right).withPC (some program.entry)) c) :
    dataBits c ≤ left.length + right.length +
      33 * (max left.length right.length + 1) + 31 := by
  have h := trace_dataBits program htrace
  have hstart : dataBits ((state regs left right).withPC (some program.entry)) =
      left.length + right.length := by
    simp [dataBits, stackBits, state, BinaryPrograms.Add.stackState, Fin.sum_univ_succ]
  rw [hstart] at h
  omega

/-- The same actual accumulator execution returns the canonical sum and has
linear all-prefix source-stack space whenever the sum is an `n`-variable count. -/
theorem canonical_execution (regs : Fin 8 → Bool) (a b n : ℕ) (hcount : a + b ≤ 2 ^ n) :
    ∃ (t : ℕ) (final : StructuredProgram.State 8 3),
      t ≤ 100 * (n + 1) ∧
      Trace program t
        ((state regs (binaryNat a) (binaryNat b)).withPC (some program.entry))
        (final.withPC none) ∧
      final.stacks 0 = binaryNat (a + b) ∧ final.stacks 1 = [] ∧ final.stacks 2 = [] ∧
      ∀ prefixSteps c, prefixSteps ≤ t →
        Trace program prefixSteps
          ((state regs (binaryNat a) (binaryNat b)).withPC (some program.entry)) c →
          dataBits c ≤ 100 * (n + 1) := by
  have ha : a ≤ 2 ^ n := (Nat.le_add_right a b).trans hcount
  have hb : b ≤ 2 ^ n := (Nat.le_add_left b a).trans hcount
  have hla := binaryNat_length_le ha
  have hlb := binaryNat_length_le hb
  have hva : CounterPrograms.value (binaryNat a) = a := by
    rw [← CanonicalWordProgram.ofDigits_eq_value, binaryNat_decode]
  have hvb : CounterPrograms.value (binaryNat b) = b := by
    rw [← CanonicalWordProgram.ofDigits_eq_value, binaryNat_decode]
  obtain ⟨final, ⟨t, ht, htrace⟩, houtput, h1, h2⟩ :=
    program_runs regs (binaryNat a) (binaryNat b)
  refine ⟨t, final, by omega, htrace, ?_, h1, h2, ?_⟩
  · simpa only [hva, hvb] using houtput
  · intro prefixSteps c hp hc
    have hs := prefix_dataBits_le regs (binaryNat a) (binaryNat b) prefixSteps c
      (hp.trans ht) hc
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.Accumulator
