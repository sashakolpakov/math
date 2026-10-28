import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramTrivial

namespace OAI.Algorithms

/-! Fixed native dispatch for the two trivial formula cases. The classifier
reads the immutable bare clause-list payload at784; the sole final answer
port is787. The nontrivial branch is the actual caller-supplied command. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Dispatch

open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := State 40 896

def registers (i : Fin 10) : Fin 40 := i.castAdd 30
def stackMap : Fin 10 → Fin 896 := ![788,789,790,791,792,793,794,795,796,784]

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective 10 30
theorem stackMap_injective : Function.Injective stackMap := by decide

abbrev classify : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram Trivial.program registers stackMap)

abbrev answer (bit : Bool) : Cmd 40 896 :=
  .seq (.base (.atom (.set 9 bit))) (.base (.atom (.push 787 9)))

abbrev command (nontrivial : Cmd 40 896) : Cmd 40 896 :=
  .seq classify (.ite 0 (answer false) (.ite 7 nontrivial (answer true)))

abbrev program (nontrivial : Cmd 40 896) := compiled (command nontrivial) 784 787

def answered (a : Data) (bit : Bool) : Data :=
  ⟨Function.update a.regs 9 bit,Function.update a.stacks 787 (bit::a.stacks 787)⟩

theorem answer_eval (a : Data) (bit : Bool) : Eval (answer bit) 2 a (answered a bit) := by
  have h1 := Eval.base (StructuredProgram.Eval.atom (.set (9 : Fin 40) bit) a)
  have h2 := Eval.base (StructuredProgram.Eval.atom (.push (787 : Fin 896) (9 : Fin 40))
    ((StructuredProgram.Atom.set (9 : Fin 40) bit).eval a))
  simpa [answer,answered,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using h1.seq h2

noncomputable def install (frame : Data) (a : Trivial.Data) : Data :=
  embedState registers stackMap frame a

theorem classify_run (frame : Data) (a : Trivial.Data) (records : List (List Bool))
    (hbody : a.stacks 9 = Encoding.encodeList id records) (hready : SubexpEmptyClauseProgram.Ready a) :
    ∃ k ≤ 100*((a.stacks 9).length+1)+3,
      Eval classify k (install frame a) (install frame (Trivial.result a records)) := by
  obtain ⟨k,hk,he⟩ := Trivial.program_run a records hbody hready
  exact ⟨k,hk,eval_call_lifted Trivial.program registers stackMap frame
    registers_injective stackMap_injective he⟩

theorem result_empty_clause (frame : Data) (a : Trivial.Data) (records : List (List Bool)) :
    (install frame (Trivial.result a records)).regs 0 = decide ([false] ∈ records) := by
  rw [show (0 : Fin 40) = registers 0 from rfl]
  rw [show (install frame (Trivial.result a records)).regs (registers 0) =
      (Trivial.result a records).regs 0 from
    embedState_register registers stackMap frame _ registers_injective 0]
  exact Trivial.result_empty_clause a records

theorem result_nonempty (frame : Data) (a : Trivial.Data) (records : List (List Bool)) :
    (install frame (Trivial.result a records)).regs 7 = decide (records ≠ []) := by
  rw [show (7 : Fin 40) = registers 7 from rfl]
  rw [show (install frame (Trivial.result a records)).regs (registers 7) =
      (Trivial.result a records).regs 7 from
    embedState_register registers stackMap frame _ registers_injective 7]
  exact Trivial.result_nonempty a records

/-- An actual empty clause immediately writes UNSAT, without invoking the
nontrivial program or depending on the ambient variable count. -/
theorem empty_clause_run (nontrivial : Cmd 40 896) (frame : Data) (a : Trivial.Data)
    (records : List (List Bool)) (hbody : a.stacks 9 = Encoding.encodeList id records)
    (hready : SubexpEmptyClauseProgram.Ready a) (he : [false] ∈ records) :
    ∃ k ≤ 100*((a.stacks 9).length+1)+6,
      Eval (command nontrivial) k (install frame a)
        (answered (install frame (Trivial.result a records)) false) := by
  obtain ⟨k,hk,hr⟩ := classify_run frame a records hbody hready
  have hb : (install frame (Trivial.result a records)).regs 0 = true := by
    rw [result_empty_clause]; exact decide_eq_true he
  exact ⟨k+(2+1),by omega,hr.seq (Eval.ite_true hb (answer_eval _ false))⟩

/-- An empty formula immediately writes SAT, including at ambient n=0. -/
theorem empty_formula_run (nontrivial : Cmd 40 896) (frame : Data) (a : Trivial.Data)
    (hbody : a.stacks 9 = Encoding.encodeList id [])
    (hready : SubexpEmptyClauseProgram.Ready a) :
    ∃ k ≤ 100*((a.stacks 9).length+1)+7,
      Eval (command nontrivial) k (install frame a)
        (answered (install frame (Trivial.result a [])) true) := by
  obtain ⟨k,hk,hr⟩ := classify_run frame a [] hbody hready
  have h0 : (install frame (Trivial.result a [])).regs 0 = false := by
    rw [result_empty_clause]; decide
  have h7 : (install frame (Trivial.result a [])).regs 7 = false := by
    rw [result_nonempty]; decide
  exact ⟨k+((2+1)+1),by omega,hr.seq
    (Eval.ite_false h0 (Eval.ite_false h7 (answer_eval _ true)))⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Dispatch

end OAI.Algorithms
