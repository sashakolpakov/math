import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgramDot

namespace OAI.Algorithms

/-! Fixed-control detection of positive-degree coefficients. The constant
coefficient is physically skipped, then every remaining two-bit cell is
read. The result is register 3; no semantic predicate is an instruction. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram

abbrev nonconstantProgram : Program 4 1 9 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := ![.pop 0 0 1 1, .pop 0 0 1 2, .set 3 false 3,
    .pop 0 0 1 4, .branch 1 5 8, .pop 0 2 1 6,
    .bor 0 0 2 7, .bor 3 3 0 3, .halt]

def nonconstantCfg (pc : Option (Fin 9)) (regs : Fin 4 → Bool)
    (input : List Bool) : Cfg 4 1 9 := ⟨pc, regs, ![input]⟩

theorem scalarBits_nonzero (a : IrreducibleSearch.F) :
    ((scalarBits a).1 || (scalarBits a).2) = decide (a ≠ 0) := by
  fin_cases a <;> decide

def nonconstantRoundRegs (regs : Fin 4 → Bool) (a : IrreducibleSearch.F) : Fin 4 → Bool :=
  let r := readRegs (readRegs regs 0 1 (some (scalarBits a).1)) 2 1 (some (scalarBits a).2)
  let r := Function.update r 0 (decide (a ≠ 0))
  Function.update r 3 (regs 3 || decide (a ≠ 0))

theorem nonconstant_round (regs : Fin 4 → Bool) (a : IrreducibleSearch.F)
    (rest : List Bool) :
    Trace nonconstantProgram 5
      (nonconstantCfg (some 3) regs (coefficientWord a ++ rest))
      (nonconstantCfg (some 3) (nonconstantRoundRegs regs a) rest) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, nonconstantProgram, nonconstantCfg,
    nonconstantRoundRegs, execInstr, readRegs, coefficientWord_eq,
    scalarBits_nonzero, Function.update_apply]
  funext i
  fin_cases i ; simp []

theorem nonconstant_exit (regs : Fin 4 → Bool) :
    Trace nonconstantProgram 3
      (nonconstantCfg (some 3) regs [])
      (nonconstantCfg none (readRegs regs 0 1 none) []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, nonconstantProgram, nonconstantCfg,
    execInstr, readRegs, Function.update_apply]

theorem nonconstant_loop (as : List IrreducibleSearch.F) (regs : Fin 4 → Bool) :
    ∃ finalRegs, Trace nonconstantProgram (5 * as.length + 3)
      (nonconstantCfg (some 3) regs (coefficientArray as))
      (nonconstantCfg none finalRegs []) ∧
      finalRegs 3 = (regs 3 || as.any (fun a => decide (a ≠ 0))) := by
  induction as generalizing regs with
  | nil =>
      refine ⟨readRegs regs 0 1 none, nonconstant_exit regs, ?_⟩
      simp [readRegs]
  | cons a as ih =>
      obtain ⟨last, ht, hv⟩ := ih (nonconstantRoundRegs regs a)
      refine ⟨last, ?_, ?_⟩
      · have he := (nonconstant_round regs a (coefficientArray as)).trans ht
        convert he using 1 <;> simp [coefficientArray_cons] ; omega
      · simpa [nonconstantRoundRegs, Bool.or_assoc] using hv

def nonconstantInitRegs (regs : Fin 4 → Bool) (a : IrreducibleSearch.F) : Fin 4 → Bool :=
  Function.update
    (readRegs (readRegs regs 0 1 (some (scalarBits a).1)) 0 1 (some (scalarBits a).2)) 3 false

theorem nonconstant_init (regs : Fin 4 → Bool) (a : IrreducibleSearch.F)
    (rest : List Bool) :
    Trace nonconstantProgram 3
      (nonconstantCfg (some 0) regs (coefficientWord a ++ rest))
      (nonconstantCfg (some 3) (nonconstantInitRegs regs a) rest) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, nonconstantProgram, nonconstantCfg,
    nonconstantInitRegs, execInstr, readRegs, coefficientWord_eq, Function.update_apply]
  funext i
  fin_cases i ; simp

theorem nonconstant_run (a : IrreducibleSearch.F) (as : List IrreducibleSearch.F)
    (regs : Fin 4 → Bool) :
    ∃ finalRegs, Trace nonconstantProgram (5 * as.length + 6)
      (nonconstantCfg (some 0) regs (coefficientArray (a :: as)))
      (nonconstantCfg none finalRegs []) ∧
      finalRegs 3 = as.any (fun x => decide (x ≠ 0)) := by
  obtain ⟨last, ht, hv⟩ := nonconstant_loop as (nonconstantInitRegs regs a)
  refine ⟨last, ?_, ?_⟩
  · have he := (nonconstant_init regs a (coefficientArray as)).trans ht
    simpa only [coefficientArray_cons,
      show 3 + (5 * as.length + 3) = 5 * as.length + 6 by omega] using he
  · simpa [nonconstantInitRegs] using hv

theorem nonconstant_tail {d : ℕ} (a : Fin (d + 1) → IrreducibleSearch.F) :
    IrreducibleSearch.nonconstant a =
      (List.ofFn fun i : Fin d => a i.succ).any (fun x => decide (x ≠ 0)) := by
  simp [IrreducibleSearch.nonconstant, List.finRange_succ,
    List.ofFn_eq_map, Function.comp_def]

theorem nonconstant_vector_run {d : ℕ} (a : Fin (d + 1) → IrreducibleSearch.F)
    (regs : Fin 4 → Bool) :
    ∃ finalRegs, Trace nonconstantProgram (5 * d + 6)
      (nonconstantCfg (some 0) regs
        (SubexpTupleRefinement.encodeTuple (SubexpEnumerationPayload.scalarCode 3) a))
      (nonconstantCfg none finalRegs []) ∧
      finalRegs 3 = IrreducibleSearch.nonconstant a := by
  have he := nonconstant_run (a 0) (List.ofFn fun i : Fin d => a i.succ) regs
  simpa only [List.length_ofFn, ← List.ofFn_succ, coefficientArray_ofFn,
    ← nonconstant_tail] using he

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
