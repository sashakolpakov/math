import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-! A four-label program computes the sign parity of a unary index. The
bits of the counter are irrelevant; only its length is used. -/

namespace SubexponentialSAT.Subexp.MatrixParityProgram

open BitProgram

abbrev program : Program 3 1 4 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 3, .bnot 2 2 0, .halt]

def toggle : ℕ → Bool → Bool
  | 0, b => b
  | n + 1, b => toggle n (!b)

def start (regs : Fin 3 → Bool) (bits : List Bool) : Cfg 3 1 4 :=
  ⟨some 0, regs, fun _ => bits⟩

def finish (b : Bool) : Cfg 3 1 4 :=
  ⟨none, ![false, false, b], fun _ => []⟩

theorem nil_trace (regs : Fin 3 → Bool) :
    Trace program 3 (start regs []) (finish (regs 2)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, start, finish, execInstr, readRegs]
  funext j
  fin_cases j <;> simp

theorem cons_trace (regs : Fin 3 → Bool) (bit : Bool) (bits : List Bool) :
    Trace program 3 (start regs (bit :: bits))
      (start ![bit, true, !(regs 2)] bits) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, start, execInstr, readRegs]
  constructor
  · funext j
    fin_cases j <;> simp
  · funext j
    fin_cases j
    rfl

theorem program_trace (regs : Fin 3 → Bool) (bits : List Bool) :
    Trace program (3 * bits.length + 3) (start regs bits)
      (finish (toggle bits.length (regs 2))) := by
  induction bits generalizing regs with
  | nil => exact nil_trace regs
  | cons bit bits ih =>
      have ht := (cons_trace regs bit bits).trans (ih ![bit, true, !(regs 2)])
      convert ht using 1
      · simp only [List.length_cons]
        omega
      · simp [toggle]

theorem program_runsIn (regs : Fin 3 → Bool) (bits : List Bool) :
    RunsIn program (3 * bits.length + 3) (start regs bits)
      (finish (toggle bits.length (regs 2))) :=
  ⟨_, le_rfl, program_trace regs bits⟩

def sign {K : Type*} [Ring K] (b : Bool) : K := if b then -1 else 1

theorem sign_toggle {K : Type*} [Ring K] (n : ℕ) (b : Bool) :
    sign (K := K) (toggle n b) = (-1 : K)^n * sign b := by
  induction n generalizing b with
  | zero => simp [toggle]
  | succ n ih =>
      rw [toggle, ih, pow_succ]
      cases b <;> simp [sign ]

theorem false_sign_toggle {K : Type*} [Ring K] (n : ℕ) :
    sign (K := K) (toggle n false) = (-1 : K)^n := by
  simpa [sign] using sign_toggle (K := K) n false

end SubexponentialSAT.Subexp.MatrixParityProgram

end OAI.Algorithms
