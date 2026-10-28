import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpExponentController

namespace OAI.Algorithms

/-! A fixed initializer for the degree-budget exponent generator.  Its only
numeric input is the unary dimension.  It preserves that input and constructs
one zero marker per coordinate and a unary budget of `2 * D + 1`. -/

namespace SubexponentialSAT.SubexpExponentSeed

open BitProgram

abbrev program : Program 2 4 14 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 8, .set 0 false 3,
    .push 1 0 4, .set 0 true 5, .push 2 0 6, .push 2 0 7,
    .push 3 0 0, .pop 3 0 1 9, .branch 1 10 11,
    .push 0 0 8, .set 0 true 12, .push 2 0 13, .halt]

def storage (dimension digits budget restore : List Bool) : Fin 4 → List Bool :=
  ![dimension, digits, budget, restore]

def cfg (pc : Option (Fin 14)) (regs : Fin 2 → Bool)
    (dimension digits budget restore : List Bool) : Cfg 2 4 14 :=
  ⟨pc, regs, storage dimension digits budget restore⟩

private theorem replicate_append_cons (n : ℕ) (a : Bool) (tail : List Bool) :
    List.replicate n a ++ a :: tail = a :: (List.replicate n a ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ] using congrArg (List.cons a) ih

theorem round_trace (regs : Fin 2 → Bool) (dimension digits budget restore : List Bool) :
    Trace program 8 (cfg (some 0) regs (true :: dimension) digits budget restore)
      (cfg (some 0) ![true, true] dimension (false :: digits)
        (true :: true :: budget) (true :: restore)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg, storage,
    readRegs, Function.update_apply]
  constructor <;> funext i <;> fin_cases i <;> simp

theorem seed_trace (D : ℕ) (regs : Fin 2 → Bool) (digits budget restore : List Bool) :
    ∃ finalRegs, Trace program (8 * D)
      (cfg (some 0) regs (List.replicate D true) digits budget restore)
      (cfg (some 0) finalRegs [] (List.replicate D false ++ digits)
        (List.replicate (2 * D) true ++ budget) (List.replicate D true ++ restore)) := by
  induction D generalizing regs digits budget restore with
  | zero => exact ⟨regs, .refl _⟩
  | succ D ih =>
    have first := round_trace regs (List.replicate D true) digits budget restore
    obtain ⟨finalRegs, rest⟩ := ih ![true, true] (false :: digits)
      (true :: true :: budget) (true :: restore)
    refine ⟨finalRegs, ?_⟩
    have total := first.trans rest
    simpa [List.replicate_succ, List.replicate_add, List.append_assoc, replicate_append_cons,
      Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using total

theorem seed_exit_trace (regs : Fin 2 → Bool) (digits budget restore : List Bool) :
    Trace program 2 (cfg (some 0) regs [] digits budget restore)
      (cfg (some 8) ![false, false] [] digits budget restore) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg, storage,
    readRegs, Function.update_apply]
  funext i; fin_cases i <;> simp

theorem restore_round_trace (regs : Fin 2 → Bool)
    (dimension digits budget restore : List Bool) :
    Trace program 3 (cfg (some 8) regs dimension digits budget (true :: restore))
      (cfg (some 8) ![true, true] (true :: dimension) digits budget restore) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg, storage,
    readRegs, Function.update_apply]
  constructor <;> funext i <;> fin_cases i <;> simp

theorem exit_trace (regs : Fin 2 → Bool) (dimension digits budget : List Bool) :
    Trace program 5 (cfg (some 8) regs dimension digits budget [])
      (cfg none ![true, false] dimension digits (true :: budget) []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg, storage,
    readRegs, Function.update_apply]
  constructor <;> funext i <;> fin_cases i <;> simp

theorem restore_trace (D : ℕ) (regs : Fin 2 → Bool) (dimension digits budget : List Bool) :
    Trace program (3 * D + 5)
      (cfg (some 8) regs dimension digits budget (List.replicate D true))
      (cfg none ![true, false] (List.replicate D true ++ dimension)
        digits (true :: budget) []) := by
  induction D generalizing regs dimension with
  | zero => exact exit_trace regs dimension digits budget
  | succ D ih =>
    have total := (restore_round_trace regs dimension digits budget
      (List.replicate D true)).trans (ih ![true, true] (true :: dimension))
    simpa [List.replicate_succ, List.replicate_add, List.append_assoc, replicate_append_cons,
      Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using total

theorem program_trace (D : ℕ) (regs : Fin 2 → Bool) :
    Trace program (11 * D + 7)
      (cfg (some program.entry) regs (List.replicate D true) [] [] [])
      (cfg none ![true, false] (List.replicate D true)
        (List.replicate D false) (List.replicate (2 * D + 1) true) []) := by
  obtain ⟨middleRegs, first⟩ := seed_trace D regs [] [] []
  simp only [List.append_nil] at first
  have total := first.trans ((seed_exit_trace middleRegs (List.replicate D false)
    (List.replicate (2 * D) true) (List.replicate D true)).trans
      (restore_trace D ![false, false] [] (List.replicate D false)
        (List.replicate (2 * D) true)))
  simpa only [List.append_nil, List.replicate_succ,
    show 8 * D + (2 + (3 * D + 5)) = 11 * D + 7 by omega]
    using total

theorem zero_digits (D : ℕ) :
    List.replicate D false =
      SubexpExponentSuccessor.digitsCode (List.replicate D 0) := by
  induction D with
  | zero => rfl
  | succ D ih => simpa [List.replicate_succ, SubexpExponentSuccessor.digitsCode] using ih

end SubexponentialSAT.SubexpExponentSeed

end OAI.Algorithms
