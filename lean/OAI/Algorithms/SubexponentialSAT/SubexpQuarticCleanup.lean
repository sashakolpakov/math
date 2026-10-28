import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BankRoutines

namespace OAI.Algorithms

/-! # Actual final workspace cleanup for the quartic coefficient producer -/

namespace SubexponentialSAT.SubexpQuarticCleanup

open BitProgram StructuredCalls

abbrev Data := State 14 35

def ports : List (Fin 35) := (List.finRange 35).filter (fun i => i != 33)
abbrev command : Cmd 14 35 := BankRoutines.clearCmd 27 0 1 ports

theorem ports_nodup : ports.Nodup := by decide
theorem ports_length : ports.length = 34 := by decide

theorem mem_ports (j : Fin 35) : j ∈ ports ↔ j ≠ 33 := by
  simp [ports]

theorem sum_lengths_le {S : Type} (xs : List S) (words : S → List Bool) (width : ℕ)
    (h : ∀ j ∈ xs, (words j).length ≤ width) :
    (xs.map (fun j => (words j).length)).sum ≤ xs.length * width := by
  induction xs with
  | nil => simp
  | cons j xs ih =>
      have hj := h j (by simp)
      have ht := ih (fun i hi => h i (by simp [hi]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

def result (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, fun j => if j = 33 then d.stacks 33 else []⟩

/-- Cleanup preserves the selected forward byte word, clears every other
stack, and charges for the actual lengths of all discarded tables. -/
theorem cleanup_eval (d : Data) (width : ℕ) (h27 : d.stacks 27 = [])
    (hwidth : ∀ j : Fin 35, j ≠ 33 → (d.stacks j).length ≤ width) :
    ∃ n, n ≤ 68 * width + 105 ∧ Eval command n d (result d) := by
  have he := BankRoutines.clear_eval 27 (0 : Fin 14) 1 ports ports_nodup d.regs d.stacks h27
  have hs := sum_lengths_le ports d.stacks width (fun j hj => hwidth j ((mem_ports j).mp hj))
  rw [ports_length] at hs
  have hresult :
      (⟨readRegs d.regs 0 1 none, BankRoutines.clearBankStacks ports d.stacks⟩ : Data) = result d := by
    congr 1
    funext j
    by_cases hj : j = 33
    · subst j
      simp [BankRoutines.clearBankStacks, mem_ports]
    · simp [BankRoutines.clearBankStacks, mem_ports, hj]
  refine ⟨2 * (ports.map (fun j => (d.stacks j).length)).sum + 3 * ports.length + 3, ?_, ?_⟩
  · rw [ports_length]
    omega
  · simpa only [command, hresult] using he

end SubexponentialSAT.SubexpQuarticCleanup

end OAI.Algorithms
