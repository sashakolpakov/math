import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-! Add precisely the uncovered-variable neutral factors. Inputs are the
unary outputs of the physical scope and variable scans. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 3 3
abbrev Code := Cmd 3 3
abbrev unary (n : ℕ) := List.replicate n true

abbrev state (r : Fin 3 → Bool) (q u a : ℕ) : Data := ⟨r, ![unary q,unary u,unary a]⟩
abbrev peek (i : Fin 3) : Code := .base (.atom (.peek i 0 1))
abbrev peeked (i : Fin 3) (d : Data) : Data := ⟨readRegs d.regs 0 1 (d.stacks i).head?,d.stacks⟩
theorem peek_eval (i : Fin 3) (d : Data) : Eval (peek i) 1 d (peeked i d) := .base (.atom _ _)

abbrev pushOne : Code := .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 2 0)))
abbrev ensureOne : Code := .seq (peek 2) (.ite 1 (.base .skip) pushOne)

theorem ensureOne_eval (r : Fin 3 → Bool) (q u a : ℕ) :
    ∃ n rf, n ≤ 4 ∧ Eval ensureOne n (state r q u a) (state rf q u (max a 1)) := by
  cases a with
  | zero =>
    let b := peeked 2 (state r q u 0)
    let rf := Function.update b.regs 0 true
    have hp : Eval pushOne 2 b (state rf q u 1) := by
      have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 3) true) b)).seq
        (Eval.base (StructuredProgram.Eval.atom (.push (2 : Fin 3) 0) _))
      convert h using 1
      apply congrArg (StructuredProgram.State.mk _)
      funext i; fin_cases i <;> simp [unary,b,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]
    exact ⟨4,rf,by omega,(peek_eval 2 _).seq
      (Eval.ite_false (by simp [unary,readRegs]) hp)⟩
  | succ a =>
    let b := peeked 2 (state r q u (a+1))
    have hm : max (a+1) 1 = a+1 := by omega
    refine ⟨2,b.regs,by omega,?_⟩
    rw [hm]
    exact (peek_eval 2 _).seq (Eval.ite_true
      (by simp [unary,readRegs,List.replicate_succ])
      (Eval.base (StructuredProgram.Eval.skip b)))

def neutralArity (a u : ℕ) : ℕ := max a (if u=0 then 0 else 1)
abbrev adjust : Code := .seq (peek 1) (.ite 1 ensureOne (.base .skip))

theorem adjust_eval (r : Fin 3 → Bool) (q u a : ℕ) :
    ∃ n rf, n ≤ 6 ∧ Eval adjust n (state r q u a) (state rf q u (neutralArity a u)) := by
  cases u with
  | zero =>
    let b := peeked 1 (state r q 0 a)
    refine ⟨2,b.regs,by omega,?_⟩
    have h := (peek_eval 1 (state r q 0 a)).seq
      (Eval.ite_false (yes := ensureOne) (show b.regs 1 = false by simp [b,unary,readRegs])
        (Eval.base (StructuredProgram.Eval.skip b)))
    simpa [neutralArity,b,peeked,state] using h
  | succ u =>
    let b := peeked 1 (state r q (u+1) a)
    obtain ⟨n,rf,hn,he⟩ := ensureOne_eval b.regs q (u+1) a
    refine ⟨1+(n+1),rf,by omega,?_⟩
    have h := (peek_eval 1 (state r q (u+1) a)).seq
      (Eval.ite_true (no := .base .skip) (show b.regs 1 = true by simp [b,unary,readRegs,List.replicate_succ]) he)
    simpa [neutralArity] using h

abbrev transfer : Code := .call (StackRoutines.transferProgram 1 0 0 1)
abbrev command : Code := .seq adjust transfer
abbrev program := compiled command 0 1

theorem command_eval (r : Fin 3 → Bool) (q u a : ℕ) :
    ∃ n rf, n ≤ 3*u+9 ∧ Eval command n (state r q u a)
      (state rf (q+u) 0 (neutralArity a u)) := by
  obtain ⟨n,ri,hn,ha⟩ := adjust_eval r q u a
  let rf := readRegs ri 0 1 none
  have ht : Eval transfer (3*u+3) (state ri q u (neutralArity a u))
      (state rf (q+u) 0 (neutralArity a u)) := by
    have h := SubexpScanPrimitives.transfer_eval
      (state ri q u (neutralArity a u)) (1 : Fin 3) 0 (0 : Fin 3) 1
      (by decide) (by decide)
    convert h using 1
    · simp [ unary]
    · apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i; fin_cases i <;>
          simp [ unary, StackRoutines.transferStacks, List.reverse_replicate, Nat.add_comm]
  exact ⟨n+(3*u+3),rf,by omega,ha.seq ht⟩

theorem program_runsIn (r : Fin 3 → Bool) (q u a : ℕ) :
    ∃ rf, RunsIn program (3*u+10)
      ((state r q u a).withPC (some program.entry))
      ((state rf (q+u) 0 (neutralArity a u)).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := command_eval r q u a
  exact ⟨rf,n+1,by omega,compiled_halt_trace he 0 1⟩
end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize

end OAI.Algorithms
