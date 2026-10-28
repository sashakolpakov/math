import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-! A native unary maximum. Consumes the new value and leaves the maximum
on the accumulator stack, using a linear number of physical bit operations. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Max
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 3 3
abbrev Code := Cmd 3 3
abbrev unary (n : ℕ) := List.replicate n true

abbrev state (r : Fin 3 → Bool) (x y z : List Bool) : Data := ⟨r, ![x,y,z]⟩
abbrev popX : Code := .base (.atom (.pop 0 0 1))
abbrev takeY : Code := .base (.atom (.pop 1 0 2))
abbrev pushZ : Code := .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 2 0)))
abbrev body : Code := .seq takeY (.seq pushZ popX)
abbrev loop : Code := .while 1 body

abbrev popped (r : Fin 3 → Bool) (x y z : List Bool) : Data :=
  state (readRegs r 0 1 x.head?) x.tail y z

theorem popX_eval (r : Fin 3 → Bool) (x y z : List Bool) :
    Eval popX 1 (state r x y z) (popped r x y z) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 3) 0 1)
    (state r x y z))) using 1
  apply congrArg (StructuredProgram.State.mk _)
  funext i; fin_cases i <;> rfl

theorem iteration (r : Fin 3 → Bool) (x y z : ℕ) :
    ∃ rf, Eval body 4 (popped r (unary (x+1)) (unary y) (unary z))
      (popped rf (unary x) (unary (y-1)) (unary (z+1))) := by
  let r1 := readRegs r 0 1 (some true)
  let r2 := readRegs r1 0 2 (unary y).head?
  let r3 := Function.update r2 0 true
  refine ⟨r3, ?_⟩
  have h1 : Eval takeY 1 (state r1 (unary x) (unary y) (unary z))
      (state r2 (unary x) (unary (y-1)) (unary z)) := by
    convert (Eval.base (StructuredProgram.Eval.atom (.pop (1 : Fin 3) 0 2)
      (state r1 (unary x) (unary y) (unary z)))) using 1
    apply congrArg (StructuredProgram.State.mk _)
    funext i; fin_cases i <;> simp [ unary, List.tail_replicate,
      StructuredProgram.Atom.instr,execInstr]
  have h2 : Eval pushZ 2 (state r2 (unary x) (unary (y-1)) (unary z))
      (state r3 (unary x) (unary (y-1)) (unary (z+1))) := by
    have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 3) true)
      (state r2 (unary x) (unary (y-1)) (unary z)))).seq
      (Eval.base (StructuredProgram.Eval.atom (.push (2 : Fin 3) 0) _))
    convert h using 1
    apply congrArg (StructuredProgram.State.mk _)
    funext i; fin_cases i <;>
      simp [unary,List.replicate_succ,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]
  exact h1.seq (h2.seq (popX_eval r3 (unary x) (unary (y-1)) (unary (z+1))))

theorem loop_eval (r : Fin 3 → Bool) (x y z : ℕ) :
    ∃ rf, Eval loop (5*x+1) (popped r (unary x) (unary y) (unary z))
      (state rf [] (unary (y-x)) (unary (z+x))) := by
  induction x generalizing r y z with
  | zero =>
      exact ⟨readRegs r 0 1 none, Eval.while_false (by rfl)⟩
  | succ x ih =>
      obtain ⟨ri,hi⟩ := iteration r x y z
      obtain ⟨rf,hr⟩ := ih ri (y-1) (z+1)
      refine ⟨rf, ?_⟩
      have h := Eval.while_true (show (popped r (unary (x+1)) (unary y) (unary z)).regs 1 = true by rfl) hi hr
      convert h using 1 <;> simp [Nat.sub_sub,Nat.add_comm,Nat.add_left_comm] ; omega

abbrev transfer : Code := .call (StackRoutines.transferProgram 2 1 0 1)
abbrev command : Code := .seq popX (.seq loop transfer)

theorem command_eval (r : Fin 3 → Bool) (x y : ℕ) :
    ∃ rf, Eval command (8*x+5) (state r (unary x) (unary y) [])
      (state rf [] (unary (max x y)) []) := by
  obtain ⟨ri,hi⟩ := loop_eval r x y 0
  let rf := readRegs ri 0 1 none
  have ht : Eval transfer (3*x+3) (state ri [] (unary (y-x)) (unary x))
      (state rf [] (unary (max x y)) []) := by
    have h := SubexpScanPrimitives.transfer_eval
      (state ri [] (unary (y-x)) (unary x)) (2 : Fin 3) 1 (0 : Fin 3) 1
      (by decide) (by decide)
    convert h using 1
    · simp [ unary]
    · apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i; fin_cases i <;>
          simp [ StackRoutines.transferStacks, unary, List.reverse_replicate]
        omega
  refine ⟨rf, ?_⟩
  simp only [Nat.zero_add] at hi
  have h := (popX_eval r (unary x) (unary y) []).seq (hi.seq ht)
  convert h using 1 ; omega

abbrev program := compiled command 0 1

theorem program_runsIn (r : Fin 3 → Bool) (x y : ℕ) :
    ∃ rf, RunsIn program (8*x+6)
      ((state r (unary x) (unary y) []).withPC (some program.entry))
      ((state rf [] (unary (max x y)) []).withPC none) := by
  obtain ⟨rf,he⟩ := command_eval r x y
  exact ⟨rf,_,by omega,compiled_halt_trace he 0 1⟩

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Max

end OAI.Algorithms
