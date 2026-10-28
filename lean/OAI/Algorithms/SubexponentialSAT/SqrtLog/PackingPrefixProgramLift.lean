import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgramRun

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingPrefixProgram

open SubexponentialSAT BitProgram StructuredCalls

structure Ports (r s : ℕ) where
  register : Fin 3 → Fin r
  stack : Fin 11 → Fin s
  register_injective : Function.Injective register
  stack_injective : Function.Injective stack

abbrev prepare {r s : ℕ} (p : Ports r s) : Cmd r s :=
  .call (ProgramLinking.liftProgram program p.register p.stack)

def Ready {r s : ℕ} (p : Ports r s) (before after : State r s) : Prop :=
  (∀ i : Fin 3, after.stacks (p.stack ⟨i.val, by omega⟩) =
    before.stacks (p.stack ⟨i.val, by omega⟩)) ∧
  after.stacks (p.stack 3) = (before.stacks (p.stack 0)).take
    ((before.stacks (p.stack 1)).length * (before.stacks (p.stack 2)).length) ∧
  after.stacks (p.stack 4) = unary (before.stacks (p.stack 1)).length ∧
  (∀ i : Fin 11, 5 ≤ i.val → after.stacks (p.stack i) = []) ∧
  (∀ i, (∀ j, p.stack j ≠ i) → after.stacks i = before.stacks i) ∧
  (∀ i, (∀ j, p.register j ≠ i) → after.regs i = before.regs i)

/-- Framed prefix preparation, preserving the persistent table, raw h and W
counters, every outside bank, and any stored incidence score outside ports. -/
theorem prepare_eval {r s : ℕ} (p : Ports r s) (a : State r s)
    (hempty : ∀ i : Fin 11, 3 ≤ i.val → a.stacks (p.stack i) = [])
    (henough : (a.stacks (p.stack 1)).length * (a.stacks (p.stack 2)).length ≤
      (a.stacks (p.stack 0)).length) :
    ∃ n ≤ budget (a.stacks (p.stack 1)).length (a.stacks (p.stack 2)).length + 1,
      ∃ b, Ready p a b ∧ Eval (prepare p) n a b := by
  let regs := a.regs ∘ p.register
  let table := a.stacks (p.stack 0)
  let count := a.stacks (p.stack 1)
  let width := a.stacks (p.stack 2)
  obtain ⟨n, hn, regs', ht⟩ := program_trace regs table count width henough
  have hin : input regs table count width = projectState p.register p.stack a := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [ table, count, width, hempty]
  rw [hin] at ht
  let b := embedState p.register p.stack a (output regs' table count width)
  have he := eval_call_from_state program p.register p.stack a p.register_injective p.stack_injective ht
  have hs : ∀ i, b.stacks (p.stack i) = (output regs' table count width).stacks i :=
    embedState_stack p.register p.stack a (output regs' table count width) p.stack_injective
  refine ⟨n, hn, b, ?_, he⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hs]
    fin_cases i <;> rfl
  · exact hs 3
  · exact hs 4
  · intro i hi
    rw [hs]
    fin_cases i <;> simp_all [output]
  · intro i hi
    exact embedState_stack_frame p.register p.stack a (output regs' table count width) i (by rintro ⟨j, hj⟩; exact hi j hj)
  · intro i hi
    exact embedState_register_frame p.register p.stack a (output regs' table count width) i (by rintro ⟨j, hj⟩; exact hi j hj)

/-- The physical prefix is recovered from the full table with padding. The
truncated prefix is an output of the command, never an input assumption. -/
theorem take_flatten_prefix (rows : List (List Bool)) (padding : List Bool) (W h : ℕ)
    (hw : ∀ row ∈ rows, row.length = W) (hh : h ≤ rows.length) :
    (rows.flatten ++ padding).take (h * W) = (rows.take h).flatten := by
  have hrows : ∀ row ∈ rows.take h, row.length = W :=
    fun row hr => hw row (List.mem_of_mem_take hr)
  have hlen := ArrayUpdatePrograms.uniform_flatten_length (rows.take h) W hrows
  simp only [List.length_take, Nat.min_eq_left hh] at hlen
  have hsplit : rows.flatten = (rows.take h).flatten ++ (rows.drop h).flatten := by
    rw [← List.flatten_append, List.take_append_drop]
  rw [hsplit, List.append_assoc, ← hlen]
  exact List.take_left

theorem prefix_capacity (rows : List (List Bool)) (padding : List Bool) (W h : ℕ)
    (hw : ∀ row ∈ rows, row.length = W) (hh : h ≤ rows.length) :
    h * W ≤ (rows.flatten ++ padding).length := by
  have hl := ArrayUpdatePrograms.uniform_flatten_length rows W hw
  rw [List.length_append, hl]
  exact (Nat.mul_le_mul_right W hh).trans (Nat.le_add_right _ _)

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
