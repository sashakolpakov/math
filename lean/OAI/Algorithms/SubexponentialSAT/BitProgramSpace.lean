import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BitProgram

namespace OAI.Algorithms

/-! Data-size bounds for the concrete Boolean-stack machine. A single
instruction can allocate at most one new bit. These bounds concern the actual
configurations on measured traces, not an auxiliary cost annotation. -/

namespace SubexponentialSAT.BitProgram

open scoped BigOperators

def stackBits {s : ℕ} (stk : Fin s → List Bool) : ℕ :=
  ∑ k, (stk k).length

theorem stackBits_update {s : ℕ} (stk : Fin s → List Bool) (k : Fin s)
    (word : List Bool) :
    stackBits (Function.update stk k word) + (stk k).length = stackBits stk + word.length := by
  have lengths : (fun i => (Function.update stk k word i).length) =
      Function.update (fun i => (stk i).length) k word.length := by
    funext i
    by_cases hi : i = k
    · subst i
      simp
    · simp only [Function.update_of_ne hi]
  unfold stackBits
  rw [lengths, Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ (fun i => (stk i).length) (Finset.mem_univ k)
  omega

def dataBits {r s l : ℕ} (c : Cfg r s l) : ℕ := stackBits c.stacks

theorem execInstr_dataBits {r s l : ℕ} (i : Instr r s l) (c : Cfg r s l) :
    dataBits (execInstr i c) ≤ dataBits c + 1 := by
  cases i <;> try simp [dataBits, execInstr]
  · rename_i stack src next
    have h := stackBits_update c.stacks stack (c.regs src :: c.stacks stack)
    simp only [List.length_cons] at h
    change stackBits (Function.update c.stacks stack (c.regs src :: c.stacks stack)) ≤ _
    omega
  · rename_i stack value present next
    have h := stackBits_update c.stacks stack (c.stacks stack).tail
    have htail : (c.stacks stack).tail.length ≤ (c.stacks stack).length := by
      cases c.stacks stack <;> simp
    change stackBits (Function.update c.stacks stack (c.stacks stack).tail) ≤ _
    omega

theorem step_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l}
    (h : step p a = some b) : dataBits b ≤ dataBits a + 1 := by
  cases hp : a.pc with
  | none => simp [step, hp] at h
  | some label =>
      simp [step, hp] at h
      rw [← h]
      exact execInstr_dataBits _ _

theorem trace_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l} {n : ℕ}
    (h : Trace p n a b) : dataBits b ≤ dataBits a + n := by
  induction h with
  | refl a => simp
  | cons hs ht ih =>
      have hstep := step_dataBits p hs
      omega

theorem runsIn_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l} {n : ℕ}
    (h : RunsIn p n a b) : dataBits b ≤ dataBits a + n := by
  obtain ⟨t, ht, htrace⟩ := h
  exact (trace_dataBits p htrace).trans (Nat.add_le_add_left ht _)

@[simp] theorem initial_dataBits {r s l : ℕ} (p : Program r s l) (input : List Bool) :
    dataBits (initial p input) = input.length := by
  simp only [dataBits, stackBits ]
  have lengths (k : Fin s) : (if k = p.inputStack then input else []).length =
      if k = p.inputStack then input.length else 0 := by split_ifs <;> rfl
  simp_rw [lengths]
  simp

theorem input_runsIn_dataBits {r s l : ℕ} (p : Program r s l)
    {input : List Bool} {b : Cfg r s l} {n : ℕ}
    (h : RunsIn p n (initial p input) b) : dataBits b ≤ input.length + n := by
  simpa using runsIn_dataBits p h

end SubexponentialSAT.BitProgram

end OAI.Algorithms
