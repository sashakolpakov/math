import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgramStorage

namespace OAI.Algorithms

/-! A fixed bit program for the dynamically long F₃ dot product. Every
coefficient is physically read and every multiply-add uses the static
64-entry bit table. The source arrays are consumed. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

def atomsCommand {R S : ℕ} : List (Atom R S) → Cmd R S
  | [] => .skip
  | a :: as => .seq (.atom a) (atomsCommand as)

def atomsResult {R S : ℕ} (as : List (Atom R S)) (d : State R S) : State R S :=
  as.foldl (fun s a => a.eval s) d

theorem atoms_eval {R S : ℕ} (as : List (Atom R S)) (d : State R S) :
    Eval (atomsCommand as) as.length d (atomsResult as d) := by
  induction as generalizing d with
  | nil => exact .skip d
  | cons a as ih =>
      simpa [atomsCommand, atomsResult, Nat.add_comm] using
        (Eval.atom a d).seq (ih (a.eval d))

@[simp] theorem coefficientWord_eq (a : IrreducibleSearch.F) :
    coefficientWord a = [(scalarBits a).1, (scalarBits a).2] :=
  (scalarBits_encoding a).symm

def dotState (as bs : List IrreducibleSearch.F) (s : IrreducibleSearch.F)
    (regs : Fin 8 → Bool) (output : List Bool) : State 8 3 :=
  ⟨Function.update (Function.update regs 4 (scalarBits s).1) 5 (scalarBits s).2,
    ![coefficientArray as, coefficientArray bs, output]⟩

def dotGuardState (as bs : List IrreducibleSearch.F) (s : IrreducibleSearch.F)
    (regs : Fin 8 → Bool) (output : List Bool) : State 8 3 :=
  (Atom.pop 0 0 6).eval (dotState as bs s regs output)

def dotReadAtoms : List (Atom 8 3) := [.pop 0 1 7, .pop 1 2 7, .pop 1 3 7]
def dotCopyAtoms : List (Atom 8 3) := [.copy 4 6, .copy 5 7]
abbrev dotScalar : Cmd 8 3 := truthTable 6 7 [0, 1, 2, 3, 4, 5] multiplyAddBits
abbrev dotBody : Cmd 8 3 :=
  .seq (atomsCommand dotReadAtoms)
    (.seq dotScalar (.seq (atomsCommand dotCopyAtoms) (.atom (.pop 0 0 6))))
abbrev dotLoop : Cmd 8 3 := .while 6 dotBody

theorem dotBody_eval (a b s : IrreducibleSearch.F)
    (as bs : List IrreducibleSearch.F) (regs : Fin 8 → Bool) (output : List Bool) :
    ∃ nextRegs, Eval dotBody 14
      (dotGuardState (a :: as) (b :: bs) s regs output)
      (dotGuardState as bs (s + a * b) nextRegs output) := by
  let d0 := dotGuardState (a :: as) (b :: bs) s regs output
  let d1 := atomsResult dotReadAtoms d0
  let d2 := writtenPair (S := 3) 6 7 (scalarBits (s + a * b)) d1
  let d3 := atomsResult dotCopyAtoms d2
  have hcalc : Eval dotScalar 8 d1 d2 := by
    have he := truthTable_eval (S := 3) (6 : Fin 8) 7 [0, 1, 2, 3, 4, 5]
      multiplyAddBits d1
    simpa [dotScalar, d1, d0, atomsResult, dotReadAtoms, dotGuardState, dotState,
      Atom.eval, Atom.instr, State.ofCfg, State.withPC, execInstr,
      readRegs, coefficientArray_cons, coefficientWord_eq, multiplyAddBits,
      scalarValue_bits, d2] using he
  have hstate : d3 = dotState as bs (s + a * b) d3.regs output := by
    change State.mk d3.regs d3.stacks = State.mk _ _
    congr 1
    · funext i
      fin_cases i <;>
        simp [d3, d2, d1, d0, atomsResult, dotCopyAtoms, dotReadAtoms,
          writtenPair, dotGuardState, dotState, Atom.eval, Atom.instr,
          State.ofCfg, execInstr, readRegs]
    · funext i
      fin_cases i <;>
        simp [d3, d2, d1, d0, atomsResult, dotCopyAtoms, dotReadAtoms,
          writtenPair, dotGuardState, dotState, Atom.eval, Atom.instr,
          State.ofCfg, execInstr, readRegs,
          coefficientArray_cons, coefficientWord_eq]
  refine ⟨d3.regs, ?_⟩
  have he := (atoms_eval dotReadAtoms d0).seq
    (hcalc.seq ((atoms_eval dotCopyAtoms d2).seq (Eval.atom (.pop 0 0 6) d3)))
  rw [hstate] at he
  simpa only [d0, dotBody, dotReadAtoms, dotCopyAtoms, List.length_cons,
    List.length_nil, Nat.reduceAdd, dotGuardState] using he

def dotAccumulator : List IrreducibleSearch.F → List IrreducibleSearch.F →
    IrreducibleSearch.F → IrreducibleSearch.F
  | a :: as, b :: bs, s => dotAccumulator as bs (s + a * b)
  | _, _, s => s

theorem dotAccumulator_value (as bs : List IrreducibleSearch.F) (s : IrreducibleSearch.F) :
    dotAccumulator as bs s = s + (List.zipWith (· * ·) as bs).sum := by
  induction as generalizing bs s with
  | nil => simp [dotAccumulator]
  | cons a as ih =>
      cases bs with
      | nil => simp [dotAccumulator]
      | cons b bs => simp [dotAccumulator, ih, add_assoc]

theorem dotLoop_eval (as bs : List IrreducibleSearch.F) (s : IrreducibleSearch.F)
    (hlen : as.length = bs.length) (regs : Fin 8 → Bool) (output : List Bool) :
    ∃ finalRegs, Eval dotLoop (15 * as.length + 1)
      (dotGuardState as bs s regs output)
      (dotGuardState [] [] (dotAccumulator as bs s) finalRegs output) := by
  induction as generalizing bs s regs with
  | nil =>
      have hb : bs = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst bs
      refine ⟨regs, ?_⟩
      apply Eval.while_false
      simp [dotGuardState, dotState, Atom.eval, Atom.instr, State.ofCfg, execInstr, readRegs]
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          obtain ⟨mid, hb⟩ := dotBody_eval a b s as bs regs output
          obtain ⟨last, ht⟩ := ih bs (s + a * b) (by simpa using hlen) mid
          refine ⟨last, ?_⟩
          have hg : (dotGuardState (a :: as) (b :: bs) s regs output).regs 6 = true := by
            simp [dotGuardState, dotState, Atom.eval, Atom.instr, State.ofCfg, execInstr, readRegs]
          have he := Eval.while_true hg hb ht
          convert he using 1 <;> simp [ dotAccumulator] ; omega

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
