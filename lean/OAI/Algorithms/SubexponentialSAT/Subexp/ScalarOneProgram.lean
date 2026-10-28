import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixWordEncoding
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! # Construct a canonical scalar one from the existing zero word -/

namespace SubexponentialSAT.Subexp.ScalarOneProgram

open BitProgram StructuredCalls

theorem fixedBits_zero (B : ℕ) :
    SubexpLiftRing.fixedBits B 0 = List.replicate B false := by
  induction B <;> simp [SubexpLiftRing.fixedBits,List.replicate_succ, *]

theorem width_pos (p : ℕ) : 0 < MatrixWordEncoding.width p := by
  simp [MatrixWordEncoding.width,SubexpLiftRing.baseWidth]

theorem word_zero (p : ℕ) :
    MatrixWordEncoding.word p 0 = List.replicate (MatrixWordEncoding.width p) false := by
  simp [MatrixWordEncoding.word,fixedBits_zero]

theorem word_one (p : ℕ) [Fact p.Prime] :
    MatrixWordEncoding.word p 1 =
      true :: List.replicate (MatrixWordEncoding.width p - 1) false := by
  have h1 : (1 : ZMod p).val = 1 := by
    rw [ZMod.val_one_eq_one_mod,Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt]
  have hp := width_pos p
  cases hB : MatrixWordEncoding.width p with
  | zero => omega
  | succ B => simp [MatrixWordEncoding.word,h1,hB,SubexpLiftRing.fixedBits,fixedBits_zero]

abbrev command {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r) : Cmd r s :=
  .seq (.call (StackRoutines.copyProgram src dst tmp value present))
    (.seq (.base (.atom (.pop dst value present)))
      (TupleProgram.pushConst dst value true))

theorem command_eval {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (B : ℕ) (a : State r s) (hs : a.stacks src = List.replicate (B + 1) false)
    (hd : a.stacks dst = []) (ht : a.stacks tmp = []) :
    ∃ regs', Eval (command src dst tmp value present) (7 * (B + 1) + 8) a
      ⟨regs',Function.update a.stacks dst (true :: List.replicate B false)⟩ := by
  let b : State r s := ⟨readRegs a.regs value present none,
    StackRoutines.copyStacks src dst a.stacks⟩
  let c := (StructuredProgram.Atom.pop dst value present).eval b
  let d := TupleProgram.pushedState dst value true c
  have h1 := TupleProgram.copy_eval src dst tmp value present hsd hst htd hvp a ht
  have h2 := Eval.base (StructuredProgram.Eval.atom (.pop dst value present) b)
  have h3 := TupleProgram.pushConst_eval dst value true c
  have hs' : d.stacks = Function.update a.stacks dst (true :: List.replicate B false) := by
    funext i
    by_cases hi : i = dst
    · subst i
      simp [d, c, b, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        execInstr, StackRoutines.copyStacks,
        hs,hd,List.replicate_succ]
    · simp [d, c, b, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        execInstr, StackRoutines.copyStacks,
        hs,hd,hi,List.replicate_succ]
  have hd' : d = ⟨d.regs,Function.update a.stacks dst (true :: List.replicate B false)⟩ := by
    exact congrArg (StructuredProgram.State.mk d.regs) hs'
  have he := h1.seq (h2.seq h3)
  change Eval _ _ a d at he
  rw [hd'] at he
  refine ⟨d.regs,?_⟩
  convert he using 1
  all_goals simp [hs]

/-- This is a real copy/pop/push computation. The modulus does not determine
the instruction table; only the existing zero word's runtime length matters. -/
theorem canonical_eval {r s : ℕ} (p : ℕ) [Fact p.Prime]
    (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (a : State r s) (hs : a.stacks src = MatrixWordEncoding.word p 0)
    (hd : a.stacks dst = []) (ht : a.stacks tmp = []) :
    ∃ regs', Eval (command src dst tmp value present)
      (7 * MatrixWordEncoding.width p + 8) a
      ⟨regs',Function.update a.stacks dst (MatrixWordEncoding.word p 1)⟩ := by
  have hB : MatrixWordEncoding.width p - 1 + 1 = MatrixWordEncoding.width p := by
    have := width_pos p
    omega
  have hz : a.stacks src = List.replicate (MatrixWordEncoding.width p - 1 + 1) false := by
    rw [hB,hs,word_zero]
  simpa only [hB,← word_one p] using
    command_eval src dst tmp value present hsd hst htd hvp
      (MatrixWordEncoding.width p - 1) a hz hd ht

end SubexponentialSAT.Subexp.ScalarOneProgram

end OAI.Algorithms
