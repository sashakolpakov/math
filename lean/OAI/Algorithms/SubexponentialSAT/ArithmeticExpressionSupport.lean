import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

namespace OAI.Algorithms

namespace SubexponentialSAT.ArithmeticExpressionSupport

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data (S : ℕ) := State 8 S

abbrev atom {S : ℕ} (a : StructuredProgram.Atom 8 S) : Cmd 8 S := .base (.atom a)

abbrev copyCmd {S : ℕ} (src dst tmp : Fin S) : Cmd 8 S :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)

theorem copy_eval {S : ℕ} (src dst tmp : Fin S) (d : Data S)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (hd : d.stacks dst = []) (ht : d.stacks tmp = []) :
    Eval (copyCmd src dst tmp) (7 * (d.stacks src).length + 5) d
      ⟨readRegs d.regs 0 1 none, Function.update d.stacks dst (d.stacks src)⟩ := by
  have h := ListRegisterProgram.copy_run src dst tmp (0 : Fin 8) 1
    hsd hst htd (by decide) d.regs d.stacks ht
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC,
    StackRoutines.copyStacks, hd] using h

abbrev clearCmd {S : ℕ} (port : Fin S) : Cmd 8 S :=
  .call (StackRoutines.clearProgram port 0 1)

theorem clear_eval {S : ℕ} (port : Fin S) (d : Data S) :
    Eval (clearCmd port) (2 * (d.stacks port).length + 3) d
      ⟨readRegs d.regs 0 1 none, Function.update d.stacks port []⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run port (0 : Fin 8) 1 d.regs d.stacks

/-- The word is part of the fixed program, rather than a runtime arithmetic operation. -/
def pushWord {S : ℕ} (dst : Fin S) : List Bool → Cmd 8 S
  | [] => .base .skip
  | b :: bs => .seq (pushWord dst bs) (.seq (atom (.set 0 b)) (atom (.push dst 0)))

theorem pushWord_eval {S : ℕ} (dst : Fin S) (bits : List Bool) (d : Data S) :
    ∃ rf : Fin 8 → Bool, Eval (pushWord dst bits) (2 * bits.length) d
      ⟨rf, Function.update d.stacks dst (bits ++ d.stacks dst)⟩ := by
  induction bits generalizing d with
  | nil =>
      refine ⟨d.regs, ?_⟩
      have hs : Function.update d.stacks dst (d.stacks dst) = d.stacks :=
        Function.update_eq_self dst d.stacks
      simpa [pushWord, hs] using Eval.base (StructuredProgram.Eval.skip d)
  | cons b bs ih =>
      obtain ⟨rf, h⟩ := ih d
      let middle : Data S := ⟨rf, Function.update d.stacks dst (bs ++ d.stacks dst)⟩
      have hset := Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 8) b) middle)
      have hpush := Eval.base (StructuredProgram.Eval.atom (.push dst (0 : Fin 8))
        ((StructuredProgram.Atom.set 0 b).eval middle))
      refine ⟨Function.update rf 0 b, ?_⟩
      simpa [pushWord, atom, middle, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
        StructuredProgram.State.withPC, execInstr, Nat.mul_add, Nat.add_assoc] using
        Eval.seq h (Eval.seq hset hpush)

theorem bits_value (n : ℕ) : BinaryArithmetic.toNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp []
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      cases b <;> simp [BinaryArithmetic.toNat, ih, Nat.bit, Nat.add_comm]

/-- A compiled child call changes only the image of its output stack.
The hypothesis is a genuine execution of the concrete child command. -/
theorem call_on_block {s S : ℕ} (c : Cmd 8 s) (input output : Fin s)
    (block : Fin s ↪ Fin S) (d : Data S) (a b : Data s) (word : List Bool)
    {n : ℕ} (h : Eval c n a b) (hr : a.regs = d.regs)
    (ha : a.stacks = d.stacks ∘ block)
    (hb : b.stacks = Function.update a.stacks output word) :
    Eval (.call (ProgramLinking.liftProgram (compiled c input output) id block)) (n + 1) d
      ⟨b.regs, Function.update d.stacks (block output) word⟩ := by
  have hrun := eval_call_lifted (compiled c input output) id block d
    Function.injective_id block.injective (compiled_halt_trace h input output)
  have hstart : embedState id block d a = d := by
    apply embedState_eq_of_ports id block d d a Function.injective_id block.injective
    · intro i
      simpa using congrFun hr i |>.symm
    · intro i hi
      exact False.elim (hi ⟨i, rfl⟩)
    · intro i
      simpa using congrFun ha i |>.symm
    · intro i hi
      rfl
  have hend : embedState id block d b =
      (⟨b.regs, Function.update d.stacks (block output) word⟩ : Data S) := by
    apply embedState_eq_of_ports id block d _ b Function.injective_id block.injective
    · intro i
      rfl
    · intro i hi
      exact False.elim (hi ⟨i, rfl⟩)
    · intro i
      rw [hb, ha]
      simp only [Function.update_apply, block.injective.eq_iff, Function.comp_apply]
    · intro i hi
      have hne : i ≠ block output := by
        intro he
        exact hi ⟨output, he.symm⟩
      simp [hne]
  simpa only [hstart, hend] using hrun

end SubexponentialSAT.ArithmeticExpressionSupport

end OAI.Algorithms
