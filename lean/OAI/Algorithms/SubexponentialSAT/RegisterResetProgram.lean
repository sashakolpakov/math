import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-! Fixed finite register initialization. The list of ports is part of the
program, not input data; every reset is one actual Boolean-register instruction. -/

namespace SubexponentialSAT.RegisterResetProgram

open BitProgram StructuredCalls

def clear {r s : ℕ} : List (Fin r) → Cmd r s
  | [] => .base .skip
  | i :: rest => .seq (.base (.atom (.set i false))) (clear rest)

def cleared {r s : ℕ} (ports : List (Fin r)) (a : State r s) : State r s :=
  ⟨fun i => if i ∈ ports then false else a.regs i, a.stacks⟩

theorem clear_eval {r s : ℕ} (ports : List (Fin r)) (a : State r s) :
    Eval (clear ports) ports.length a (cleared ports a) := by
  induction ports generalizing a with
  | nil =>
      have he : cleared [] a = a := by cases a; rfl
      rw [he]
      exact .base (.skip _)
  | cons i rest ih =>
      let b : State r s := ⟨Function.update a.regs i false, a.stacks⟩
      have hfirst : Eval (.base (.atom (.set i false))) 1 a b :=
        .base (.atom _ _)
      have hlast : cleared rest b = cleared (i :: rest) a := by
        apply congrArg₂ StructuredProgram.State.mk
        · funext j
          by_cases hj : j = i <;> by_cases hr : j ∈ rest <;>
            simp [ b, hj, hr ]
        · rfl
      have h := hfirst.seq (ih b)
      rw [hlast] at h
      simpa only [clear, List.length_cons, Nat.add_comm] using h

theorem clear_size {r s : ℕ} (ports : List (Fin r)) : size (@clear r s ports) = ports.length := by
  induction ports with
  | nil => rfl
  | cons i rest ih => simp [clear, size, StructuredProgram.size, ih, Nat.add_comm]

abbrev all {r s : ℕ} : Cmd r s := clear (List.finRange r)

abbrev zeroed {r s : ℕ} (a : State r s) : State r s := ⟨fun _ => false, a.stacks⟩

theorem all_eval {r s : ℕ} (a : State r s) : Eval all r a (zeroed a) := by
  have h := clear_eval (List.finRange r) a
  have he : cleared (List.finRange r) a = zeroed a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      simp [ ]
    · rfl
  simpa only [all, List.length_finRange, he] using h

@[simp] theorem all_size (r s : ℕ) : size (@all r s) = r := by
  simp [all, clear_size]

abbrev program {r s : ℕ} (port : Fin s) : Program r s (size (@all r s) + 1) :=
  compiled all port port

theorem program_trace {r s : ℕ} (port : Fin s) (a : State r s) :
    Trace (program (r := r) port) (r + 1)
      (a.withPC (some (program (r := r) port).entry)) ((zeroed a).withPC none) := by
  exact compiled_halt_trace (all_eval a) port port

end SubexponentialSAT.RegisterResetProgram

end OAI.Algorithms
