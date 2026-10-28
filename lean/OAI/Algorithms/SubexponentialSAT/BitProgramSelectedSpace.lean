import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

namespace OAI.Algorithms

/-!
# Stack-bit growth inside a fixed set of ports

Every actual instruction adds at most one bit to any fixed set of stacks.
These bounds exclude unselected persistent stacks, whose contents may be
arbitrarily long. The list corollaries require distinct ports, as used by the
physical workspace cleanup program.
-/

namespace SubexponentialSAT.BitProgram

open scoped BigOperators

def selectedStackBits {s : ℕ} (ports : Finset (Fin s))
    (stk : Fin s → List Bool) : ℕ :=
  ∑ k ∈ ports, (stk k).length

theorem selectedStackBits_update_le {s : ℕ} (ports : Finset (Fin s))
    (stk : Fin s → List Bool) (k : Fin s) (word : List Bool)
    (hword : word.length ≤ (stk k).length + 1) :
    selectedStackBits ports (Function.update stk k word) ≤ selectedStackBits ports stk + 1 := by
  have lengths : (fun i => (Function.update stk k word i).length) =
      Function.update (fun i => (stk i).length) k word.length := by
    funext i
    by_cases hi : i = k
    · subst i
      simp
    · simp only [Function.update_of_ne hi]
  unfold selectedStackBits
  rw [lengths]
  by_cases hk : k ∈ ports
  · rw [Finset.sum_update_of_mem hk, Finset.sdiff_singleton_eq_erase]
    have hsum := Finset.sum_erase_add ports (fun i => (stk i).length) hk
    omega
  · rw [Finset.sum_update_of_notMem hk]
    omega

theorem execInstr_selectedStackBits {r s l : ℕ} (ports : Finset (Fin s))
    (i : Instr r s l) (c : Cfg r s l) :
    selectedStackBits ports (execInstr i c).stacks ≤ selectedStackBits ports c.stacks + 1 := by
  cases i <;> try simp [execInstr]
  · rename_i stack src next
    exact selectedStackBits_update_le ports c.stacks stack
      (c.regs src :: c.stacks stack) (by simp)
  · rename_i stack value present next
    apply selectedStackBits_update_le ports c.stacks stack (c.stacks stack).tail
    cases c.stacks stack <;> simp ; omega

theorem step_selectedStackBits {r s l : ℕ} (p : Program r s l)
    (ports : Finset (Fin s)) {a b : Cfg r s l} (h : step p a = some b) :
    selectedStackBits ports b.stacks ≤ selectedStackBits ports a.stacks + 1 := by
  cases hp : a.pc with
  | none => simp [step, hp] at h
  | some label =>
      simp [step, hp] at h
      rw [← h]
      exact execInstr_selectedStackBits ports _ _

theorem trace_selectedStackBits {r s l : ℕ} (p : Program r s l)
    (ports : Finset (Fin s)) {a b : Cfg r s l} {n : ℕ} (h : Trace p n a b) :
    selectedStackBits ports b.stacks ≤ selectedStackBits ports a.stacks + n := by
  induction h with
  | refl a => simp
  | cons hs ht ih =>
      have hstep := step_selectedStackBits p ports hs
      omega

theorem runsIn_selectedStackBits {r s l : ℕ} (p : Program r s l)
    (ports : Finset (Fin s)) {a b : Cfg r s l} {n : ℕ} (h : RunsIn p n a b) :
    selectedStackBits ports b.stacks ≤ selectedStackBits ports a.stacks + n := by
  obtain ⟨t, ht, htrace⟩ := h
  exact (trace_selectedStackBits p ports htrace).trans (Nat.add_le_add_left ht _)

theorem selectedStackBits_toFinset {s : ℕ} (ports : List (Fin s))
    (hnodup : ports.Nodup) (stk : Fin s → List Bool) :
    selectedStackBits ports.toFinset stk = (ports.map (fun i => (stk i).length)).sum :=
  List.sum_toFinset (fun i => (stk i).length) hnodup

/-- List form matching the exact cost of clearing distinct selected ports. -/
theorem trace_listStackBits {r s l : ℕ} (p : Program r s l)
    (ports : List (Fin s)) (hnodup : ports.Nodup)
    {a b : Cfg r s l} {n : ℕ} (h : Trace p n a b) :
    (ports.map (fun i => (b.stacks i).length)).sum ≤
      (ports.map (fun i => (a.stacks i).length)).sum + n := by
  simpa only [selectedStackBits_toFinset ports hnodup] using
    trace_selectedStackBits p ports.toFinset h

theorem runsIn_listStackBits {r s l : ℕ} (p : Program r s l)
    (ports : List (Fin s)) (hnodup : ports.Nodup)
    {a b : Cfg r s l} {n : ℕ} (h : RunsIn p n a b) :
    (ports.map (fun i => (b.stacks i).length)).sum ≤
      (ports.map (fun i => (a.stacks i).length)).sum + n := by
  simpa only [selectedStackBits_toFinset ports hnodup] using
    runsIn_selectedStackBits p ports.toFinset h

end SubexponentialSAT.BitProgram

end OAI.Algorithms
