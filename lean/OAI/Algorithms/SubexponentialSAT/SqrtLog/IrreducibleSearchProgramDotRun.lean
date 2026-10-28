import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgramDot

namespace OAI.Algorithms

/-! Complete execution of the fixed F₃ dot product, including initialization,
serialization of its output, the final halt, and primitive simulation. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

def dotInitialAtoms : List (Atom 8 3) := [.set 4 false, .set 5 false, .pop 0 0 6]
def dotFinalAtoms : List (Atom 8 3) := [.push 2 5, .push 2 4]
abbrev dotCommand : Cmd 8 3 :=
  .seq (atomsCommand dotInitialAtoms) (.seq dotLoop (atomsCommand dotFinalAtoms))
abbrev dotProgram : Program 8 3 (size dotCommand + 1) := compiled dotCommand 0 2

def dotInput (as bs : List IrreducibleSearch.F) (regs : Fin 8 → Bool)
    (output : List Bool) : State 8 3 :=
  ⟨regs, ![coefficientArray as, coefficientArray bs, output]⟩

theorem dotInitial_result (as bs : List IrreducibleSearch.F)
    (regs : Fin 8 → Bool) (output : List Bool) :
    atomsResult dotInitialAtoms (dotInput as bs regs output) =
      dotGuardState as bs 0 regs output := by
  have hz : scalarBits (0 : IrreducibleSearch.F) = (false, false) := by decide
  simp [atomsResult, dotInitialAtoms, dotInput, dotGuardState, dotState,
    Atom.eval, Atom.instr, State.ofCfg, execInstr, hz]

theorem dotFinal_result (s : IrreducibleSearch.F)
    (regs : Fin 8 → Bool) (output : List Bool) :
    atomsResult dotFinalAtoms (dotGuardState [] [] s regs output) =
      ⟨(dotGuardState [] [] s regs output).regs,
        ![[], [], coefficientWord s ++ output]⟩ := by
  simp [atomsResult, dotFinalAtoms, dotGuardState, dotState,
    Atom.eval, Atom.instr, State.ofCfg, execInstr,
    readRegs, coefficientWord_eq]
  funext i
  fin_cases i <;> simp

theorem dotCommand_eval (as bs : List IrreducibleSearch.F)
    (hlen : as.length = bs.length) (regs : Fin 8 → Bool) (output : List Bool) :
    ∃ finalRegs, Eval dotCommand (15 * as.length + 6)
      (dotInput as bs regs output)
      ⟨finalRegs, ![[], [], coefficientWord ((List.zipWith (· * ·) as bs).sum) ++ output]⟩ := by
  have hi := atoms_eval dotInitialAtoms (dotInput as bs regs output)
  rw [dotInitial_result] at hi
  obtain ⟨last, hl⟩ := dotLoop_eval as bs 0 hlen regs output
  have hf := atoms_eval dotFinalAtoms
    (dotGuardState [] [] (dotAccumulator as bs 0) last output)
  rw [dotFinal_result] at hf
  refine ⟨(dotGuardState [] [] (dotAccumulator as bs 0) last output).regs, ?_⟩
  have he := hi.seq (hl.seq hf)
  convert he using 1 <;>
    simp [ dotInitialAtoms, dotFinalAtoms, dotAccumulator_value] ; omega

theorem dotProgram_run (as bs : List IrreducibleSearch.F)
    (hlen : as.length = bs.length) (regs : Fin 8 → Bool) (output : List Bool) :
    ∃ finalRegs, Trace dotProgram (15 * as.length + 7)
      ((dotInput as bs regs output).withPC (some dotProgram.entry))
      (State.withPC
        ⟨finalRegs, ![[], [], coefficientWord ((List.zipWith (· * ·) as bs).sum) ++ output]⟩ none) := by
  obtain ⟨last, he⟩ := dotCommand_eval as bs hlen regs output
  refine ⟨last, ?_⟩
  simpa [dotProgram, Nat.add_assoc] using compiled_halt_trace he 0 2

theorem dotProgram_primitive (as bs : List IrreducibleSearch.F)
    (hlen : as.length = bs.length) (regs : Fin 8 → Bool) (output : List Bool) :
    ∃ finalRegs, Computation.RunsIn (primitive dotProgram).step
      (primitiveOverhead dotProgram * (15 * as.length + 7))
      (primitiveCfg dotProgram ((dotInput as bs regs output).withPC (some dotProgram.entry)))
      (primitiveCfg dotProgram (State.withPC
        ⟨finalRegs, ![[], [], coefficientWord ((List.zipWith (· * ·) as bs).sum) ++ output]⟩ none)) := by
  obtain ⟨last, he⟩ := dotProgram_run as bs hlen regs output
  exact ⟨last, BitProgram.primitive_execution dotProgram ⟨_, Nat.le_refl _, he⟩⟩

def convolutionLeft {d : ℕ} (a : Fin d → IrreducibleSearch.F) (j : ℕ) :=
  List.ofFn (fun i : Fin (j + 1) => IrreducibleSearch.entry a i)
def convolutionRight {d : ℕ} (b : Fin d → IrreducibleSearch.F) (j : ℕ) :=
  List.ofFn (fun i : Fin (j + 1) => IrreducibleSearch.entry b (j - i))

theorem zipWith_ofFn {A B C : Type*} (f : A → B → C) (n : ℕ) :
    ∀ (a : Fin n → A) (b : Fin n → B),
      List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => f (a i) (b i)) := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
      intro a b
      simp only [List.ofFn_succ, List.zipWith_cons_cons]
      rw [ih]

theorem convolution_dot {d : ℕ} (a b : Fin d → IrreducibleSearch.F) (j : ℕ) :
    (List.zipWith (· * ·) (convolutionLeft a j) (convolutionRight b j)).sum =
      IrreducibleSearch.convolution a b j := by
  unfold convolutionLeft convolutionRight
  rw [zipWith_ofFn, List.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range (fun i =>
    IrreducibleSearch.entry a i * IrreducibleSearch.entry b (j - i)) (j + 1)

/-- The dot-product body computes exactly a search convolution coefficient.
This theorem exposes, rather than hides, its prepared coefficient streams.
Constructing those streams remains a separately charged stage. -/
theorem convolutionProgram_run {d : ℕ} (a b : Fin d → IrreducibleSearch.F)
    (j : ℕ) (regs : Fin 8 → Bool) (output : List Bool) :
    ∃ finalRegs, Trace dotProgram (15 * (j + 1) + 7)
      ((dotInput (convolutionLeft a j) (convolutionRight b j) regs output).withPC
        (some dotProgram.entry))
      (State.withPC
        ⟨finalRegs, ![[], [], coefficientWord (IrreducibleSearch.convolution a b j) ++ output]⟩ none) := by
  have h := dotProgram_run (convolutionLeft a j) (convolutionRight b j)
    (by simp [convolutionLeft, convolutionRight]) regs output
  rw [convolution_dot] at h
  have hl : (convolutionLeft a j).length = j + 1 := by simp [convolutionLeft]
  simpa only [hl] using h

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
