import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixPositionProgram

namespace OAI.Algorithms

/-! One physical active-position step for a normalized matrix entry.
Stack 2 counts unchanged nonfixed pairs, stack 3 counts swapped nonfixed
pairs, and register 7 records compatibility of all positions seen so far. -/

namespace SubexponentialSAT.Subexp.MatrixPositionCountProgram

open BitProgram StructuredCalls StackRoutines MatrixPositionProgram

abbrev popResult (out : Fin 8) : Cmd 8 17 := .base (.atom (.pop 11 out 5))
def popped (a : Data) (out : Fin 8) : Data :=
  ⟨readRegs a.regs out 5 (a.stacks 11).head?, Function.update a.stacks 11 (a.stacks 11).tail⟩

theorem popResult_eval (a : Data) (out : Fin 8) : Eval (popResult out) 1 a (popped a out) :=
  .base (.atom _ _)

abbrev branch : Cmd 8 17 :=
  .ite 6 (.ite 4 (.base .skip) (TupleProgram.pushConst 2 0 true))
    (.ite 4 (TupleProgram.pushConst 3 0 true) (.base (.atom (.set 7 false))))

def branched (a : Data) : Data :=
  if a.regs 6 then
    if a.regs 4 then a else TupleProgram.pushedState 2 0 true a
  else if a.regs 4 then TupleProgram.pushedState 3 0 true a
  else (StructuredProgram.Atom.set (7 : Fin 8) false).eval a

theorem branch_eval (a : Data) : ∃ n ≤ 4, Eval branch n a (branched a) := by
  cases h6 : a.regs 6 <;> cases h4 : a.regs 4
  · refine ⟨3, by decide, ?_⟩
    simpa only [branch, branched, h6, h4, Bool.false_eq_true, ↓reduceIte] using
      Eval.ite_false h6 (Eval.ite_false h4 (Eval.base (StructuredProgram.Eval.atom
        (StructuredProgram.Atom.set (7 : Fin 8) false) a)))
  · refine ⟨4, by decide, ?_⟩
    simpa only [branch, branched, h6, h4, Bool.false_eq_true, ↓reduceIte] using
      Eval.ite_false h6 (Eval.ite_true h4 (TupleProgram.pushConst_eval (3 : Fin 17) (0 : Fin 8) true a))
  · refine ⟨4, by decide, ?_⟩
    simpa only [branch, branched, h6, h4, Bool.false_eq_true, ↓reduceIte] using
      Eval.ite_true h6 (Eval.ite_false h4 (TupleProgram.pushConst_eval (2 : Fin 17) (0 : Fin 8) true a))
  · refine ⟨2, by decide, ?_⟩
    simpa only [branch, branched, h6, h4, ↓reduceIte] using
      Eval.ite_true h6 (Eval.ite_true h4 (Eval.base (StructuredProgram.Eval.skip a)))

abbrev reset : Cmd 8 17 :=
  .seq (.base (.atom (.set 0 false))) (.seq (.base (.atom (.set 4 false)))
    (.seq (.base (.atom (.set 5 false))) (.base (.atom (.set 6 false)))))

def resetState (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update (Function.update a.regs
    0 false) 4 false) 5 false) 6 false, a.stacks⟩

theorem reset_eval (a : Data) : Eval reset 4 a (resetState a) := by
  let a1 := (StructuredProgram.Atom.set (0 : Fin 8) false).eval a
  let a2 := (StructuredProgram.Atom.set (4 : Fin 8) false).eval a1
  let a3 := (StructuredProgram.Atom.set (5 : Fin 8) false).eval a2
  have h := (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (0 : Fin 8) false) a)).seq
    ((Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (4 : Fin 8) false) a1)).seq
      ((Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (5 : Fin 8) false) a2)).seq
        (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (6 : Fin 8) false) a3))))
  simpa [reset, resetState, a3, a2, a1, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

abbrev command : Cmd 8 17 :=
  .seq (comparePair false) (.seq (popResult 6) (.seq (comparePair true)
    (.seq (popResult 4) (.seq branch reset))))

def classified (a : Data) : Data :=
  let same := pairMatches a false
  let swapped := pairMatches a true
  ⟨fun j => if j = 7 then a.regs 7 && (same || swapped) else false,
    Function.update (Function.update a.stacks 2
      (if same && !swapped then true :: a.stacks 2 else a.stacks 2)) 3
      (if swapped && !same then true :: a.stacks 3 else a.stacks 3)⟩

private theorem pairMatches_popped_compared (a : Data) (answer : Bool)
    (out : Fin 8) (swapped : Bool) :
    pairMatches (popped (compared a answer) out) swapped = pairMatches a swapped := by
  cases swapped <;> simp [pairMatches, leftWord, popped ]

private theorem volume_popped_compared (a : Data) (answer : Bool) (out : Fin 8) :
    volume (popped (compared a answer) out) = volume a := by
  simp [volume, popped ]

private theorem compared_regs_eq (a : Data) (answer : Bool) :
    (compared a answer).regs =
      ![false, false, false, false, false, a.regs 5, a.regs 6, a.regs 7] := by
  funext j
  fin_cases j <;> norm_num [compared]

private theorem compared_stacks_eq (a : Data) (answer : Bool) :
    (compared a answer).stacks =
      Function.update (Function.update (Function.update a.stacks 1 []) 12 [])
        11 (answer :: a.stacks 11) := rfl

theorem command_eval (a : Data)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (h11 : a.stacks 11 = []) (h12 : a.stacks 12 = []) :
    ∃ n ≤ 36 * volume a + 90, Eval command n a (classified a) := by
  let a1 := compared a (pairMatches a false)
  let a2 := popped a1 6
  let a3 := compared a2 (pairMatches a true)
  let a4 := popped a3 4
  let a5 := branched a4
  obtain ⟨n1, hn1, t1⟩ := comparePair_eval a false h0 h1 h12
  have t2 := popResult_eval a1 6
  obtain ⟨n3, hn3, t3⟩ := comparePair_eval a2 true
    (by simp [a2, a1, popped, h0])
    (by simp [a2, a1, popped ])
    (by simp [a2, a1, popped ])
  have hmatch : pairMatches a2 true = pairMatches a true :=
    pairMatches_popped_compared a (pairMatches a false) 6 true
  rw [hmatch] at t3
  have t4 := popResult_eval a3 4
  obtain ⟨n5, hn5, t5⟩ := branch_eval a4
  have t6 := reset_eval a5
  have hfinish : resetState a5 = classified a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      cases hs : pairMatches a false <;> cases hw : pairMatches a true <;> fin_cases j <;>
        simp [a5, a4, a3, a2, a1, branched, popped, hs, hw, readRegs, h11,
          TupleProgram.pushedState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
    · funext j
      cases hs : pairMatches a false <;> cases hw : pairMatches a true <;> fin_cases j <;>
        simp [a5, a4, a3, a2, a1, branched, popped, hs, hw, readRegs, h1, h11, h12,
          TupleProgram.pushedState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
  rw [hfinish] at t6
  refine ⟨n1 + (1 + (n3 + (1 + (n5 + 4)))), ?_,
    t1.seq (t2.seq (t3.seq (t4.seq (t5.seq t6))))⟩
  have hv : volume a2 = volume a := volume_popped_compared a (pairMatches a false) 6
  rw [hv] at hn3
  omega

abbrev program : Program 8 17 (size command + 1) := compiled command 13 2

theorem program_runsIn (a : Data)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (h11 : a.stacks 11 = []) (h12 : a.stacks 12 = []) :
    RunsIn program (36 * volume a + 91)
      (a.withPC (some program.entry)) ((classified a).withPC none) := by
  obtain ⟨n, hn, ht⟩ := command_eval a h0 h1 h11 h12
  exact ⟨n + 1, by omega, compiled_halt_trace ht 13 2⟩

theorem classified_stack_frame (a : Data) (j : Fin 17) (h2 : j ≠ 2) (h3 : j ≠ 3) :
    (classified a).stacks j = a.stacks j := by simp [classified, h2, h3]

end SubexponentialSAT.Subexp.MatrixPositionCountProgram

end OAI.Algorithms
