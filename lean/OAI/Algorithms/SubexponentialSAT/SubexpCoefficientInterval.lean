import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCoefficientEntries
import OAI.Algorithms.SubexponentialSAT.SubexpIntervalStartProgram
import OAI.Algorithms.SubexponentialSAT.SubexpIntervalStart

namespace OAI.Algorithms

/-! Actual binary interval initialization in the coefficient work bank. -/

namespace SubexponentialSAT.SubexpCoefficientProgram

open BitProgram StructuredCalls SubexpSetupStorage SubexpSetupBoundSpec
open SubexpCoefficientStaging Subexp

abbrev initializer : Stage where
  registers := 8
  stackCount := 32
  labels := size SubexpIntervalStartProgram.command + 1
  program := SubexpIntervalStartProgram.program
  register_le := by decide
  stack_le := by decide
  inputs := [(41, 0), (42, 1), (43, 2)]
  inputs_length := by decide
  inputs_nodup := by decide
  source_high := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> decide
  target_low := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> decide
  output := 3
  destination := 44
  destination_high := by decide

private theorem initial_word (regs : SubexpIntervalCoreProgram.Regs)
    (r Q R : List Bool) (i : Fin 32) :
    (SubexpIntervalStartProgram.initialState regs r Q R).stacks i =
      if i = 0 then r else if i = 1 then Q else if i = 2 then R else [] := by
  fin_cases i <;> rfl

theorem initializer_entry (a : Data) :
    project initializer.register initializer.stack (initializer.prepared a) =
      SubexpIntervalStartProgram.initialState
        ((initializer.prepared a).regs ∘ initializer.register)
        (a.stacks 41) (a.stacks 42) (a.stacks 43) := by
  apply initializer.project_eq a
  · intro i
    rfl
  · intro p hp j hj
    change p ∈ [(41, 0), (42, 1), (43, 2)] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · have hj' : j = (0 : Fin 32) := Fin.ext (congrArg (fun i : Fin 64 => i.val) hj)
      subst j
      rfl
    · have hj' : j = (1 : Fin 32) := Fin.ext (congrArg (fun i : Fin 64 => i.val) hj)
      subst j
      rfl
    · have hj' : j = (2 : Fin 32) := Fin.ext (congrArg (fun i : Fin 64 => i.val) hj)
      subst j
      rfl
  · intro j hj
    have h0 : j ≠ (0 : Fin 32) := by
      intro h
      subst j
      exact hj (41, 0) (by change (41, 0) ∈ [(41, 0), (42, 1), (43, 2)]; simp) rfl
    have h1 : j ≠ (1 : Fin 32) := by
      intro h
      subst j
      exact hj (42, 1) (by change (42, 1) ∈ [(41, 0), (42, 1), (43, 2)]; simp) rfl
    have h2 : j ≠ (2 : Fin 32) := by
      intro h
      subst j
      exact hj (43, 2) (by change (43, 2) ∈ [(41, 0), (42, 1), (43, 2)]; simp) rfl
    rw [initial_word, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2]

def initializerBound (B : ℕ) : ℕ := 10000 * (3 * B + 1)^2 + 1

theorem initializer_run (r Q R B : ℕ) (hr : 0 < r) (a : Data) (ha : WordBound B a)
    (hrw : CounterPrograms.value (a.stacks 41) = r)
    (hQw : CounterPrograms.value (a.stacks 42) = Q)
    (hRw : CounterPrograms.value (a.stacks 43) = R) :
    ∃ t b, Eval initializer.command t a b ∧
      t ≤ 400 * (B + initializerBound B + 1) ∧ WordBound (B + initializerBound B) b ∧
      CounterPrograms.value (b.stacks 44) = SubexpIntervalStart.value r Q R ∧
      (∀ i : Fin 64, 32 ≤ i.val → i ≠ 63 → i ≠ 44 → b.stacks i = a.stacks i) := by
  have hpos : 0 < BinaryArithmetic.toNat (a.stacks 41) := by
    simpa only [← CounterPrograms.value_eq_toNat, hrw] using hr
  obtain ⟨out, he, _, _, _, hv, _, _⟩ := SubexpIntervalStartProgram.run_value
    ((initializer.prepared a).regs ∘ initializer.register)
    (a.stacks 41) (a.stacks 42) (a.stacks 43) hpos
  rw [← initializer_entry] at he
  have hwidth : SubexpIntervalCoreProgram.width (a.stacks 41) (a.stacks 42) (a.stacks 43) ≤
      3 * B + 1 := by
    have h1 := ha 41
    have h2 := ha 42
    have h3 := ha 43
    unfold SubexpIntervalCoreProgram.width
    omega
  have hbudget : SubexpIntervalStartProgram.runtimeBound
      (a.stacks 41) (a.stacks 42) (a.stacks 43) ≤ initializerBound B := by
    unfold SubexpIntervalStartProgram.runtimeBound initializerBound
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hwidth 2)) 1
  obtain ⟨steps, hs, ht⟩ := he
  obtain ⟨t, et, htime, hw⟩ := initializer.run a out B (initializerBound B) ha
    ⟨steps, hs.trans hbudget, ht⟩
  refine ⟨t, initializer.result a out, et, htime, hw, ?_,
    fun i hi h63 h44 => initializer.result_frame a out i hi h63 h44⟩
  have hout := initializer.result_output a out
  change (initializer.result a out).stacks 44 = out.stacks 3 at hout
  rw [hout]
  simpa only [← CounterPrograms.value_eq_toNat, hrw, hQw, hRw,
    SubexpIntervalStartProgram.value, SubexpIntervalStart.value] using hv


end SubexponentialSAT.SubexpCoefficientProgram

end OAI.Algorithms
