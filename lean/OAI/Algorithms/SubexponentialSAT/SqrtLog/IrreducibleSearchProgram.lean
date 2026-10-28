import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgramLift
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgramNonconstant
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgramCompare
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! Closed fixed-bit F₃ factor checker. The complete command is independent
of the degree. All coefficient addresses and loop bounds are runtime unary
words; source vectors are preserved and scratch stacks are discharged. -/


/-! Coefficient -/

/-! A fixed coefficient kernel: two preserved source arrays, a preserved
unary coefficient address plus one, and an output stack. Every copy, padded
prefix, coefficient reversal, multiply-add and cleanup is an actual call. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

def sixRegisters : Fin 6 ↪ Fin 16 :=
  ⟨fun i => ⟨i.val, by omega⟩, by intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h⟩
def eightRegisters : Fin 8 ↪ Fin 16 :=
  ⟨fun i => ⟨i.val, by omega⟩, by intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h⟩
def coefficientLeftPorts : Fin 3 ↪ Fin 11 := ⟨![3, 5, 6], by decide⟩
def coefficientReversePorts : Fin 3 ↪ Fin 11 := ⟨![6, 5, 7], by decide⟩
def coefficientRightPorts : Fin 3 ↪ Fin 11 := ⟨![4, 5, 8], by decide⟩
def coefficientDotPorts : Fin 3 ↪ Fin 11 := ⟨![7, 8, 9], by decide⟩

abbrev coefficientCommand : Cmd 16 11 :=
  .seq (copyCmd 0 3 10) <| .seq (copyCmd 2 5 10) <|
  .seq (prefixCall sixRegisters coefficientLeftPorts) <| .seq (copyCmd 2 5 10) <|
  .seq (prefixCall sixRegisters coefficientReversePorts) <| .seq (copyCmd 1 4 10) <|
  .seq (copyCmd 2 5 10) <| .seq (prefixCall sixRegisters coefficientRightPorts) <|
  .seq (dotCall eightRegisters coefficientDotPorts) <| .seq (clearCmd 3) (clearCmd 4)

def coefficientState (as bs : List IrreducibleSearch.F) (count output : List Bool)
    (regs : Fin 16 → Bool) : State 16 11 :=
  ⟨regs, ![coefficientArray as, coefficientArray bs, count,
    [], [], [], [], [], [], output, []]⟩

def coefficientValue (as bs : List IrreducibleSearch.F) (n : ℕ) : IrreducibleSearch.F :=
  (List.zipWith (· * ·) (paddedPrefix n as) (paddedPrefix n bs).reverse).sum

theorem coefficientCommand_eval (as bs : List IrreducibleSearch.F)
    (count output : List Bool) (regs : Fin 16 → Bool) :
    ∃ steps finalRegs, steps ≤ 300 * (as.length + bs.length + count.length + 1) ∧
      Eval coefficientCommand steps (coefficientState as bs count output regs)
        (coefficientState as bs count
          (coefficientWord (coefficientValue as bs count.length) ++ output) finalRegs) := by
  let d0 := coefficientState as bs count output regs
  let d1 := copyState (0 : Fin 11) 3 d0
  have e1 := copy_eval (0 : Fin 11) 3 10 d0 (by decide) (by decide) (by decide)
    (by simp [d0, coefficientState])
  let d2 := copyState (2 : Fin 11) 5 d1
  have e2 := copy_eval (2 : Fin 11) 5 10 d1 (by decide) (by decide) (by decide)
    (by simp [d1, d0, copyState, StackRoutines.copyStacks, coefficientState])
  obtain ⟨r3, e3⟩ := prefixCall_eval sixRegisters coefficientLeftPorts as count [] d2
    (by simp [d2, d1, d0, copyState, StackRoutines.copyStacks, coefficientState,
      coefficientLeftPorts])
    (by simp [d2, d1, d0, copyState, StackRoutines.copyStacks, coefficientState,
      coefficientLeftPorts])
    (by simp [d2, d1, d0, copyState, StackRoutines.copyStacks, coefficientState,
      coefficientLeftPorts])
  let d3 := afterThree sixRegisters coefficientLeftPorts r3
    (coefficientArray (as.drop count.length)) []
    (coefficientArray (paddedPrefix count.length as).reverse) d2
  simp only [List.append_nil] at e3
  change Eval _ _ _ d3 at e3
  let d4 := copyState (2 : Fin 11) 5 d3
  have e4 := copy_eval (2 : Fin 11) 5 10 d3 (by decide) (by decide) (by decide)
    (by simp [d3, d2, d1, d0, afterThree, replaceThree, coefficientLeftPorts,
      copyState, StackRoutines.copyStacks, coefficientState])
  obtain ⟨r5, e5⟩ := prefixCall_eval sixRegisters coefficientReversePorts
    (paddedPrefix count.length as).reverse count [] d4
    (by simp [d4, d3, copyState, StackRoutines.copyStacks, afterThree, replaceThree,
      coefficientReversePorts, coefficientLeftPorts])
    (by simp [d4, d3, d2, d1, d0, copyState, StackRoutines.copyStacks, afterThree,
      replaceThree, coefficientReversePorts, coefficientLeftPorts, coefficientState])
    (by simp [d4, d3, d2, d1, d0, copyState, StackRoutines.copyStacks, afterThree,
      replaceThree, coefficientReversePorts, coefficientLeftPorts, coefficientState])
  have hlen : ((paddedPrefix count.length as).reverse).length = count.length := by simp
  have hdrop : (paddedPrefix count.length as).reverse.drop count.length = [] :=
    List.drop_eq_nil_iff.mpr hlen.le
  have hpad : paddedPrefix count.length (paddedPrefix count.length as).reverse =
      (paddedPrefix count.length as).reverse := paddedPrefix_of_length _ _ hlen
  simp only [hdrop, hpad, List.reverse_reverse, coefficientArray_nil, List.append_nil] at e5
  let d5 := afterThree sixRegisters coefficientReversePorts r5 [] []
    (coefficientArray (paddedPrefix count.length as)) d4
  change Eval _ _ _ d5 at e5
  let d6 := copyState (1 : Fin 11) 4 d5
  have e6 := copy_eval (1 : Fin 11) 4 10 d5 (by decide) (by decide) (by decide)
    (by simp [d5, d4, d3, d2, d1, d0, copyState, StackRoutines.copyStacks,
      afterThree, replaceThree, coefficientLeftPorts, coefficientReversePorts, coefficientState])
  let d7 := copyState (2 : Fin 11) 5 d6
  have e7 := copy_eval (2 : Fin 11) 5 10 d6 (by decide) (by decide) (by decide)
    (by simp [d6, d5, d4, d3, d2, d1, d0, copyState, StackRoutines.copyStacks,
      afterThree, replaceThree, coefficientLeftPorts, coefficientReversePorts, coefficientState])
  obtain ⟨r8, e8⟩ := prefixCall_eval sixRegisters coefficientRightPorts bs count [] d7
    (by simp [d7, d6, d5, d4, d3, d2, d1, d0, copyState, StackRoutines.copyStacks,
      afterThree, replaceThree, coefficientLeftPorts, coefficientReversePorts,
      coefficientRightPorts, coefficientState])
    (by simp [d7, d6, d5, d4, d3, d2, d1, d0, copyState, StackRoutines.copyStacks,
      afterThree, replaceThree, coefficientLeftPorts, coefficientReversePorts,
      coefficientRightPorts, coefficientState])
    (by simp [d7, d6, d5, d4, d3, d2, d1, d0, copyState, StackRoutines.copyStacks,
      afterThree, replaceThree, coefficientLeftPorts, coefficientReversePorts,
      coefficientRightPorts, coefficientState])
  let d8 := afterThree sixRegisters coefficientRightPorts r8
    (coefficientArray (bs.drop count.length)) []
    (coefficientArray (paddedPrefix count.length bs).reverse) d7
  simp only [List.append_nil] at e8
  change Eval _ _ _ d8 at e8
  obtain ⟨r9, e9⟩ := dotCall_eval eightRegisters coefficientDotPorts
    (paddedPrefix count.length as) (paddedPrefix count.length bs).reverse (by simp) output d8
    (by simp [d8, d7, d6, d5, copyState, StackRoutines.copyStacks, afterThree,
      replaceThree, coefficientRightPorts, coefficientReversePorts, coefficientDotPorts])
    (by simp [d8, afterThree, replaceThree, coefficientRightPorts, coefficientDotPorts])
    (by simp [d8, d7, d6, d5, d4, d3, d2, d1, d0, copyState, StackRoutines.copyStacks,
      afterThree, replaceThree, coefficientLeftPorts, coefficientReversePorts,
      coefficientRightPorts, coefficientDotPorts, coefficientState])
  let d9 := afterThree eightRegisters coefficientDotPorts r9 [] []
    (coefficientWord (coefficientValue as bs count.length) ++ output) d8
  change Eval _ _ _ d9 at e9
  let d10 := clearState (3 : Fin 11) d9
  let d11 := clearState (4 : Fin 11) d10
  have e10 := clear_eval (3 : Fin 11) d9
  have e11 := clear_eval (4 : Fin 11) d10
  have he := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq
    (e8.seq (e9.seq (e10.seq e11)))))))))
  have hend : d11 = coefficientState as bs count
      (coefficientWord (coefficientValue as bs count.length) ++ output) d11.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i
    fin_cases i <;>
      simp [d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0,
        clearState, copyState, StackRoutines.copyStacks, afterThree, replaceThree,
        coefficientLeftPorts, coefficientReversePorts, coefficientRightPorts,
        coefficientDotPorts, coefficientState]
  change Eval coefficientCommand _ d0 d11 at he
  rw [hend] at he
  refine ⟨_, d11.regs, ?_, he⟩
  have ha : (as.drop count.length).length ≤ as.length := by simp
  have hb : (bs.drop count.length).length ≤ bs.length := by simp
  simp [d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0, clearState, copyState,
    StackRoutines.copyStacks, afterThree, replaceThree, coefficientLeftPorts,
    coefficientReversePorts, coefficientRightPorts, coefficientDotPorts,
    coefficientState, coefficientArray_length]
  omega

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! CoefficientRun -/

/-! The closed, fixed-program boundary for one arbitrary convolution
coefficient. Its sources and runtime unary address are preserved and all
work stacks are empty again. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev coefficientProgram : Program 16 11 (size coefficientCommand + 1) :=
  compiled coefficientCommand 0 9

theorem coefficientProgram_run (as bs : List IrreducibleSearch.F)
    (count output : List Bool) (regs : Fin 16 → Bool) :
    ∃ finalRegs, RunsIn coefficientProgram
      (300 * (as.length + bs.length + count.length + 1) + 1)
      ((coefficientState as bs count output regs).withPC (some coefficientProgram.entry))
      ((coefficientState as bs count
        (coefficientWord (coefficientValue as bs count.length) ++ output) finalRegs).withPC none) := by
  obtain ⟨steps, last, hb, he⟩ := coefficientCommand_eval as bs count output regs
  exact ⟨last, steps + 1, by omega, compiled_halt_trace he 0 9⟩

theorem coefficientProgram_primitive (as bs : List IrreducibleSearch.F)
    (count output : List Bool) (regs : Fin 16 → Bool) :
    ∃ finalRegs, Computation.RunsIn (primitive coefficientProgram).step
      (primitiveOverhead coefficientProgram *
        (300 * (as.length + bs.length + count.length + 1) + 1))
      (primitiveCfg coefficientProgram
        ((coefficientState as bs count output regs).withPC (some coefficientProgram.entry)))
      (primitiveCfg coefficientProgram ((coefficientState as bs count
        (coefficientWord (coefficientValue as bs count.length) ++ output) finalRegs).withPC none)) := by
  obtain ⟨last, he⟩ := coefficientProgram_run as bs count output regs
  exact ⟨last, BitProgram.primitive_execution coefficientProgram he⟩

theorem coefficientValue_convolution {d : ℕ}
    (a b : Fin d → IrreducibleSearch.F) (j : ℕ) :
    coefficientValue (List.ofFn a) (List.ofFn b) (j + 1) =
      IrreducibleSearch.convolution a b j := by
  unfold coefficientValue
  rw [paddedPrefix_convolutionLeft, paddedPrefix_convolutionRight, convolution_dot]

theorem convolutionKernel_run {d : ℕ} (a b : Fin d → IrreducibleSearch.F)
    (j : ℕ) (count output : List Bool) (hc : count.length = j + 1)
    (regs : Fin 16 → Bool) :
    ∃ finalRegs, RunsIn coefficientProgram (300 * (2 * d + j + 2) + 1)
      ((coefficientState (List.ofFn a) (List.ofFn b) count output regs).withPC
        (some coefficientProgram.entry))
      ((coefficientState (List.ofFn a) (List.ofFn b) count
        (coefficientWord (IrreducibleSearch.convolution a b j) ++ output) finalRegs).withPC none) := by
  have he := coefficientProgram_run (List.ofFn a) (List.ofFn b) count output regs
  simpa only [hc, coefficientValue_convolution, List.length_ofFn,
    show d + d + (j + 1) + 1 = 2 * d + j + 2 by omega] using he

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! ProductLift -/

/-! A framed invocation of the source-preserving coefficient kernel. The
extra stack stores the remaining runtime product length. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def coefficientStackPorts : Fin 11 ↪ Fin 12 :=
  ⟨fun i => ⟨i.val, by omega⟩, by intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 12 => x.val) h⟩

def productState (as bs : List IrreducibleSearch.F) (count remaining output : List Bool)
    (regs : Fin 16 → Bool) : State 16 12 :=
  ⟨regs, ![coefficientArray as, coefficientArray bs, count,
    [], [], [], [], [], [], output, [], remaining]⟩

theorem product_embed (as bs : List IrreducibleSearch.F)
    (count remaining output newOutput : List Bool) (regs finalRegs : Fin 16 → Bool) :
    embedState id coefficientStackPorts (productState as bs count remaining output regs)
      (coefficientState as bs count newOutput finalRegs) =
      productState as bs count remaining newOutput finalRegs := by
  apply embedState_eq_of_ports id coefficientStackPorts _ _ _
    Function.injective_id coefficientStackPorts.injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have h : i = 11 := by
      apply Fin.ext
      by_contra hn
      have hv : i.val < 11 := by omega
      exact hi ⟨⟨i.val, hv⟩, rfl⟩
    subst i
    simp [productState]

abbrev coefficientCall : Cmd 16 12 :=
  .call (ProgramLinking.liftProgram coefficientProgram id coefficientStackPorts)

theorem coefficientCall_eval (as bs : List IrreducibleSearch.F)
    (count remaining output : List Bool) (regs : Fin 16 → Bool) :
    ∃ steps finalRegs, steps ≤ 300 * (as.length + bs.length + count.length + 1) + 1 ∧
      Eval coefficientCall steps (productState as bs count remaining output regs)
        (productState as bs count remaining
          (coefficientWord (coefficientValue as bs count.length) ++ output) finalRegs) := by
  obtain ⟨rf, steps, hb, he⟩ := coefficientProgram_run as bs count output regs
  have ht := eval_call_lifted coefficientProgram id coefficientStackPorts
    (productState as bs count remaining output regs) Function.injective_id
    coefficientStackPorts.injective he
  rw [product_embed, product_embed] at ht
  exact ⟨steps, rf, hb, ht⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Product -/

/-! A fixed outer loop runs the coefficient kernel at successively longer
unary addresses. Source arrays are preserved; all output coefficients are
physically written in decreasing degree order. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StructuredProgram (Atom)

def productGuardState (as bs : List IrreducibleSearch.F)
    (count remaining output : List Bool) (regs : Fin 16 → Bool) : State 16 12 :=
  (Atom.pop 11 14 15).eval (productState as bs count remaining output regs)

def productIncrement : List (Atom 16 12) := [.set 14 false, .push 2 14]
abbrev productBody : Cmd 16 12 := .seq coefficientCall <|
  .seq (.base (atomsCommand productIncrement)) (.base (.atom (.pop 11 14 15)))
abbrev productLoop : Cmd 16 12 := .while 15 productBody

theorem productBody_eval (as bs : List IrreducibleSearch.F)
    (count remaining output : List Bool) (bit : Bool) (regs : Fin 16 → Bool) :
    ∃ steps nextRegs, steps ≤ 300 * (as.length + bs.length + count.length + 1) + 4 ∧
      Eval productBody steps
        (productGuardState as bs count (bit :: remaining) output regs)
        (productGuardState as bs (false :: count) remaining
          (coefficientWord (coefficientValue as bs count.length) ++ output) nextRegs) := by
  let d0 := productGuardState as bs count (bit :: remaining) output regs
  have hd0 : d0 = productState as bs count remaining output d0.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i; fin_cases i <;>
      simp [d0, productGuardState, productState, Atom.eval, Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, readRegs]
  obtain ⟨steps, rf, hb, he⟩ := coefficientCall_eval as bs count remaining output d0.regs
  rw [← hd0] at he
  let d1 := productState as bs count remaining
    (coefficientWord (coefficientValue as bs count.length) ++ output) rf
  let d2 := atomsResult productIncrement d1
  have hd2 : d2 = productState as bs (false :: count) remaining
      (coefficientWord (coefficientValue as bs count.length) ++ output) d2.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i; fin_cases i <;>
      simp [d2, d1, atomsResult, productIncrement, productState, Atom.eval,
        Atom.instr, StructuredProgram.State.ofCfg,
        execInstr, readRegs]
  have hi := Eval.base (atoms_eval productIncrement d1)
  have hp := Eval.base (StructuredProgram.Eval.atom (.pop 11 14 15) d2)
  have ht := he.seq (hi.seq hp)
  rw [hd2] at ht
  refine ⟨steps + 3, d2.regs, by omega, ?_⟩
  simpa only [d0, productBody, productIncrement, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.add_assoc, productGuardState] using ht

def productOutput (as bs : List IrreducibleSearch.F) : ℕ → ℕ → List Bool → List Bool
  | _, 0, output => output
  | start, n + 1, output => productOutput as bs (start + 1) n
      (coefficientWord (coefficientValue as bs start) ++ output)

theorem productLoop_eval (as bs : List IrreducibleSearch.F)
    (count remaining output : List Bool) (regs : Fin 16 → Bool) :
    ∃ steps finalRegs,
      steps ≤ remaining.length *
        (300 * (as.length + bs.length + count.length + remaining.length + 1) + 5) + 1 ∧
      Eval productLoop steps (productGuardState as bs count remaining output regs)
        (productGuardState as bs (List.replicate remaining.length false ++ count) []
          (productOutput as bs count.length remaining.length output) finalRegs) := by
  induction remaining generalizing count output regs with
  | nil =>
      refine ⟨1, regs, by simp, ?_⟩
      simp only [List.length_nil, List.replicate_zero, List.nil_append, productOutput]
      apply Eval.while_false
      simp [productGuardState, productState, Atom.eval, Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, readRegs]
  | cons bit remaining ih =>
      obtain ⟨n, middle, hn, he⟩ := productBody_eval as bs count remaining output bit regs
      obtain ⟨m, last, hm, ht⟩ := ih (false :: count)
        (coefficientWord (coefficientValue as bs count.length) ++ output) middle
      have hg : (productGuardState as bs count (bit :: remaining) output regs).regs 15 = true := by
        simp [productGuardState, productState, Atom.eval, Atom.instr,
          StructuredProgram.State.ofCfg, execInstr, readRegs]
      have hr := Eval.while_true hg he ht
      refine ⟨n + m + 1, last, ?_, ?_⟩
      · simp only [List.length_cons] at hm ⊢
        nlinarith
      · simpa only [productLoop, List.length_cons, productOutput,
          List.append_assoc, List.singleton_append,
          List.replicate_succ', List.cons_append, List.nil_append] using hr

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! ProductRun -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StructuredProgram (Atom)

abbrev productCommand : Cmd 16 12 :=
  .seq (.base (.atom (.pop 11 14 15))) productLoop

abbrev productProgram : Program 16 12 (size productCommand + 1) :=
  compiled productCommand 0 9

theorem productProgram_run (as bs : List IrreducibleSearch.F)
    (count remaining output : List Bool) (regs : Fin 16 → Bool) :
    ∃ finalRegs, RunsIn productProgram
      (remaining.length *
        (300 * (as.length + bs.length + count.length + remaining.length + 1) + 5) + 3)
      ((productState as bs count remaining output regs).withPC (some productProgram.entry))
      ((productState as bs (List.replicate remaining.length false ++ count) []
        (productOutput as bs count.length remaining.length output) finalRegs).withPC none) := by
  obtain ⟨n, rf, hb, he⟩ := productLoop_eval as bs count remaining output regs
  have hi := Eval.base (StructuredProgram.Eval.atom (.pop 11 14 15)
    (productState as bs count remaining output regs))
  have ht := hi.seq he
  let last := productGuardState as bs (List.replicate remaining.length false ++ count) []
    (productOutput as bs count.length remaining.length output) rf
  have hl : last = productState as bs (List.replicate remaining.length false ++ count) []
      (productOutput as bs count.length remaining.length output) last.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i; fin_cases i <;>
      simp [last, productGuardState, productState, Atom.eval, Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, readRegs]
  change Eval productCommand (1 + n) _ last at ht
  rw [hl] at ht
  exact ⟨last.regs, 1 + n + 1, by omega, compiled_halt_trace ht 0 9⟩

theorem productOutput_value (as bs : List IrreducibleSearch.F) (start n : ℕ)
    (output : List Bool) :
    productOutput as bs start n output =
      coefficientArray (((List.range' start n).map (coefficientValue as bs)).reverse) ++ output := by
  induction n generalizing start output with
  | zero => simp [productOutput]
  | succ n ih =>
      simp [productOutput, ih, List.range'_succ, List.reverse_cons,
        coefficientArray_append, coefficientArray_cons, List.append_assoc]

theorem productOutput_convolution {d : ℕ} (a b : Fin d → IrreducibleSearch.F)
    (n : ℕ) (output : List Bool) :
    productOutput (List.ofFn a) (List.ofFn b) 1 n output =
      coefficientArray (((List.range n).map (IrreducibleSearch.convolution a b)).reverse) ++ output := by
  rw [productOutput_value]
  congr 3
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_map, List.getElem_range', List.getElem_range, Nat.one_mul]
  simpa only [Nat.add_comm, Nat.one_mul, Nat.mul_one] using coefficientValue_convolution a b i

theorem convolutionProduct_run {d : ℕ} (a b : Fin d → IrreducibleSearch.F)
    (remaining output : List Bool) (regs : Fin 16 → Bool) :
    ∃ finalRegs, RunsIn productProgram
      (remaining.length * (300 * (2 * d + remaining.length + 2) + 5) + 3)
      ((productState (List.ofFn a) (List.ofFn b) [false] remaining output regs).withPC
        (some productProgram.entry))
      ((productState (List.ofFn a) (List.ofFn b)
        (List.replicate remaining.length false ++ [false]) []
        (coefficientArray (((List.range remaining.length).map
          (IrreducibleSearch.convolution a b)).reverse) ++ output) finalRegs).withPC none) := by
  have ht := productProgram_run (List.ofFn a) (List.ofFn b) [false] remaining output regs
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, List.length_ofFn,
    show d + d + 1 + remaining.length + 1 = 2 * d + remaining.length + 2 by omega,
    productOutput_convolution] using ht

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Monic -/

/-! Appending the implicit monic coefficient uses two physical transfers.
No input-dependent instruction table or uncharged array append is used. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StructuredProgram (Atom)

abbrev transferCommand {S : ℕ} (src dst : Fin S) : Cmd 16 S :=
  .call (StackRoutines.transferProgram src dst 0 1)
def transferState {S : ℕ} (src dst : Fin S) (d : State 16 S) : State 16 S :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

theorem transferCommand_eval {S : ℕ} (src dst : Fin S) (hne : src ≠ dst)
    (d : State 16 S) :
    Eval (transferCommand src dst) (3 * (d.stacks src).length + 3) d
      (transferState src dst d) := by
  exact Eval.call _ (ListRegisterProgram.transfer_run src dst (0 : Fin 16) 1
    hne (by decide) d.regs d.stacks)

def monicAtoms {S : ℕ} (src : Fin S) : List (Atom 16 S) :=
  [.set 2 false, .push src 2, .set 2 true, .push src 2]
abbrev appendOneCommand {S : ℕ} (src tmp : Fin S) : Cmd 16 S :=
  .seq (transferCommand src tmp) <|
    .seq (.base (atomsCommand (monicAtoms src))) (transferCommand tmp src)

theorem appendOneCommand_eval {S : ℕ} (src tmp : Fin S) (hne : src ≠ tmp)
    (cs : List IrreducibleSearch.F) (d : State 16 S)
    (hsrc : d.stacks src = coefficientArray cs) (htmp : d.stacks tmp = []) :
    ∃ rf, Eval (appendOneCommand src tmp) (12 * cs.length + 10) d
      ⟨rf, Function.update d.stacks src (coefficientArray (cs ++ [1]))⟩ := by
  let d1 := transferState src tmp d
  let d2 := atomsResult (monicAtoms src) d1
  let d3 := transferState tmp src d2
  have he := (transferCommand_eval src tmp hne d).seq
    ((Eval.base (atoms_eval (monicAtoms src) d1)).seq
      (transferCommand_eval tmp src hne.symm d2))
  have hl : (d2.stacks tmp).length = 2 * cs.length := by
    simp [d2, d1, atomsResult, monicAtoms, transferState, StackRoutines.transferStacks,
      Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      execInstr, hne, hne.symm, hsrc, htmp, coefficientArray_length]
  have hs : d3.stacks = Function.update d.stacks src (coefficientArray (cs ++ [1])) := by
    funext i
    by_cases hi : i = src
    · subst i
      simp [d3, d2, d1, transferState, StackRoutines.transferStacks, atomsResult,
        monicAtoms, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr, hne, hne.symm, hsrc, htmp,
        coefficientArray_append, coefficientArray_cons, coefficientWord_eq, scalarBits] ; decide
    · by_cases hit : i = tmp
      · subst i
        simp [d3, d2, d1, transferState, StackRoutines.transferStacks, atomsResult,
          monicAtoms, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr, hne, hne.symm, htmp]
      · simp [d3, d2, d1, transferState, StackRoutines.transferStacks, atomsResult,
          monicAtoms, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr, hi, hit]
  refine ⟨d3.regs, ?_⟩
  have hd : d3 = ⟨d3.regs, Function.update d.stacks src (coefficientArray (cs ++ [1]))⟩ := by
    exact SubexpScanPrimitives.state_ext rfl hs
  change Eval (appendOneCommand src tmp) _ d d3 at he
  rw [hd] at he
  simpa only [hl, hsrc, coefficientArray_length, monicAtoms, List.length_cons,
    List.length_nil, Nat.reduceAdd, show 3 * (2 * cs.length) + 3 +
      (4 + (3 * (2 * cs.length) + 3)) = 12 * cs.length + 10 by omega] using he

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! MonicAlgebra -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram

theorem monicArray_entry {d : ℕ} (c : Fin d → IrreducibleSearch.F) (j : ℕ) :
    ((List.ofFn c ++ [1])[j]?).getD 0 = IrreducibleSearch.candidateEntry c j := by
  by_cases hj : j < d
  · simp [List.getElem?_append, hj, IrreducibleSearch.candidateEntry,
      IrreducibleSearch.entry, show j ≠ d by omega]
  · by_cases he : j = d
    · subst j
      simp [ IrreducibleSearch.candidateEntry, IrreducibleSearch.entry]
    · have hgt : d < j := by omega
      have hz : 0 < j - d := by omega
      have hn : ([1] : List IrreducibleSearch.F)[j-d]? = none :=
        List.getElem?_eq_none (by simp only [List.length_cons, List.length_nil]; omega)
      simp [List.getElem?_append, hj, he, hn,
        IrreducibleSearch.candidateEntry, IrreducibleSearch.entry]

theorem monicArray_padded {d : ℕ} (c : Fin d → IrreducibleSearch.F) (n : ℕ) :
    paddedPrefix n (List.ofFn c ++ [1]) =
      List.ofFn (fun i : Fin n => IrreducibleSearch.candidateEntry c i) := by
  apply List.ext_getElem?
  intro i
  rw [paddedPrefix_getElem?]
  by_cases hi : i < n
  · simp [ hi, monicArray_entry]
  · simp [ hi]

theorem coefficientArray_injective : Function.Injective coefficientArray :=
  StackEncoding.encodeDataStack_injective (SubexpEnumerationPayload.scalarCode 3)

theorem productComparison_eq {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (a b : Fin (d + 1) → IrreducibleSearch.F) :
    decide (coefficientArray (((List.range (2 * d + 1)).map
        (IrreducibleSearch.convolution a b)).reverse) =
      coefficientArray (paddedPrefix (2 * d + 1) (List.ofFn c ++ [1])).reverse) =
      IrreducibleSearch.productEq c a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, coefficientArray_injective.eq_iff, List.reverse_inj,
    monicArray_padded, IrreducibleSearch.productEq, List.all_eq_true,
    List.mem_range, decide_eq_true_eq]
  constructor
  · intro h j hj
    have he := congrArg (fun xs => xs[j]?) h
    rw [List.getElem?_map, List.getElem?_range hj, Option.map_some,
      List.getElem?_ofFn, dite_eq_left hj] at he
    exact Option.some.inj he
  · intro h
    apply List.ext_getElem (by simp)
    intro j hj hj'
    simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
      h j (by simpa only [List.length_map, List.length_range] using hj)

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! CheckLift -/

/-! Framed calls to the physical Boolean predicates. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def fourRegisters : Fin 4 ↪ Fin 16 :=
  ⟨fun i => ⟨i.val, by omega⟩, by
    intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h⟩

def replaceTwo {S : ℕ} (ports : Fin 2 ↪ Fin S) (a b : List Bool)
    (stk : Fin S → List Bool) : Fin S → List Bool :=
  Function.update (Function.update stk (ports 0) a) (ports 1) b
noncomputable def afterTwo {r R S : ℕ} (regs : Fin r ↪ Fin R) (ports : Fin 2 ↪ Fin S)
    (rf : Fin r → Bool) (a b : List Bool) (d : State R S) : State R S :=
  ⟨Function.extend regs rf d.regs, replaceTwo ports a b d.stacks⟩

theorem two_embed {r R S : ℕ} (regs : Fin r ↪ Fin R) (ports : Fin 2 ↪ Fin S)
    (rf : Fin r → Bool) (a b : List Bool) (d : State R S) :
    embedState regs ports d ⟨rf, ![a, b]⟩ = afterTwo regs ports rf a b d := by
  apply embedState_eq_of_ports regs ports d _ _ regs.injective ports.injective
  · intro i; exact regs.injective.extend_apply _ _ _
  · intro i hi; exact Function.extend_apply' _ _ _ hi
  · intro i; fin_cases i <;> simp [afterTwo, replaceTwo, ports.injective.eq_iff]
  · intro i hi
    have h0 : i ≠ ports 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ ports 1 := fun h => hi ⟨1, h.symm⟩
    simp [afterTwo, replaceTwo, h0, h1]

theorem two_initial {r R S : ℕ} (regs : Fin r ↪ Fin R) (ports : Fin 2 ↪ Fin S)
    (a b : List Bool) (d : State R S)
    (ha : d.stacks (ports 0) = a) (hb : d.stacks (ports 1) = b) :
    embedState regs ports d ⟨fun i => d.regs (regs i), ![a, b]⟩ = d := by
  apply embedState_eq_of_ports regs ports d _ _ regs.injective ports.injective
  · intro i; rfl
  · intros; rfl
  · intro i; fin_cases i <;> assumption
  · intros; rfl

abbrev compareCall {S : ℕ} (ports : Fin 2 ↪ Fin S) : Cmd 16 S :=
  .call (ProgramLinking.liftProgram compareProgram fourRegisters ports)

theorem compareCall_eval {S : ℕ} (ports : Fin 2 ↪ Fin S)
    (a b : List Bool) (hlen : a.length = b.length) (d : State 16 S)
    (ha : d.stacks (ports 0) = a) (hb : d.stacks (ports 1) = b) :
    ∃ rf, Eval (compareCall ports) (6 * a.length + 4) d
        (afterTwo fourRegisters ports rf [] [] d) ∧
      (afterTwo fourRegisters ports rf [] [] d).regs 3 = decide (a = b) := by
  obtain ⟨rf, he, hv⟩ := compare_run a b hlen (fun i => d.regs (fourRegisters i))
  have ht := eval_call_lifted compareProgram fourRegisters ports d
    fourRegisters.injective ports.injective
    (a := ⟨fun i => d.regs (fourRegisters i), ![a, b]⟩)
    (b := ⟨rf, ![[], []]⟩) he
  change Eval (compareCall ports) _
    (embedState fourRegisters ports d ⟨fun i => d.regs (fourRegisters i), ![a, b]⟩)
    (embedState fourRegisters ports d ⟨rf, ![[], []]⟩) at ht
  rw [two_initial _ _ _ _ _ ha hb, two_embed] at ht
  refine ⟨rf, ht, ?_⟩
  change Function.extend fourRegisters rf d.regs (fourRegisters 3) = _
  rw [fourRegisters.injective.extend_apply]
  exact hv

noncomputable def afterOne {r R S : ℕ} (regs : Fin r ↪ Fin R) (port : Fin S)
    (rf : Fin r → Bool) (a : List Bool) (d : State R S) : State R S :=
  ⟨Function.extend regs rf d.regs, Function.update d.stacks port a⟩
def onePort {S : ℕ} (port : Fin S) : Fin 1 ↪ Fin S :=
  ⟨fun _ => port, by intro i j _; exact Subsingleton.elim i j⟩

theorem one_embed {r R S : ℕ} (regs : Fin r ↪ Fin R) (port : Fin S)
    (rf : Fin r → Bool) (a : List Bool) (d : State R S) :
    embedState regs (onePort port) d ⟨rf, fun _ => a⟩ = afterOne regs port rf a d := by
  apply embedState_eq_of_ports regs (onePort port) d _ _ regs.injective (onePort port).injective
  · intro i; exact regs.injective.extend_apply _ _ _
  · intro i hi; exact Function.extend_apply' _ _ _ hi
  · intro i
    fin_cases i
    change Function.update d.stacks port a port = a
    simp
  · intro i hi
    have h : i ≠ port := fun h => hi ⟨0, h.symm⟩
    simp [afterOne, h]

theorem one_initial {r R S : ℕ} (regs : Fin r ↪ Fin R) (port : Fin S)
    (a : List Bool) (d : State R S) (ha : d.stacks port = a) :
    embedState regs (onePort port) d ⟨fun i => d.regs (regs i), fun _ => a⟩ = d := by
  apply embedState_eq_of_ports regs (onePort port) d _ _ regs.injective (onePort port).injective
  · intro i; rfl
  · intros; rfl
  · intro i; exact ha
  · intros; rfl

abbrev nonconstantCall {S : ℕ} (port : Fin S) : Cmd 16 S :=
  .call (ProgramLinking.liftProgram nonconstantProgram fourRegisters (onePort port))

theorem nonconstantCall_eval {S d : ℕ} (port : Fin S)
    (a : Fin (d + 1) → IrreducibleSearch.F) (s : State 16 S)
    (ha : s.stacks port = coefficientArray (List.ofFn a)) :
    ∃ rf, Eval (nonconstantCall port) (5 * d + 6) s
        (afterOne fourRegisters port rf [] s) ∧
      (afterOne fourRegisters port rf [] s).regs 3 = IrreducibleSearch.nonconstant a := by
  obtain ⟨rf, he, hv⟩ := nonconstant_vector_run a (fun i => s.regs (fourRegisters i))
  have hf (x : List Bool) : (![x] : Fin 1 → List Bool) = (fun _ => x) := by
    funext i; fin_cases i; rfl
  simp only [nonconstantCfg, hf] at he
  have ht := eval_call_lifted nonconstantProgram fourRegisters (onePort port) s
    fourRegisters.injective (onePort port).injective
    (a := ⟨fun i => s.regs (fourRegisters i), fun _ => coefficientArray (List.ofFn a)⟩)
    (b := ⟨rf, fun _ => []⟩) he
  change Eval (nonconstantCall port) _
    (embedState fourRegisters (onePort port) s
      ⟨fun i => s.regs (fourRegisters i), fun _ => coefficientArray (List.ofFn a)⟩)
    (embedState fourRegisters (onePort port) s ⟨rf, fun _ => []⟩) at ht
  rw [one_initial _ _ _ _ ha, one_embed] at ht
  refine ⟨rf, ht, ?_⟩
  change Function.extend fourRegisters rf s.regs (fourRegisters 3) = _
  rw [fourRegisters.injective.extend_apply]
  exact hv

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! PairProduct -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StructuredProgram (Atom)
open SubexponentialSAT.SubexpSetupStorage

def pairProductPorts : Fin 12 ↪ Fin 18 :=
  ⟨fun i => ⟨i.val, by omega⟩, by
    intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 18 => x.val) h⟩

def pairState (as bs cs : List IrreducibleSearch.F) (depth count remaining output : List Bool)
    (regs : Fin 16 → Bool) : State 16 18 :=
  ⟨regs, ![coefficientArray as, coefficientArray bs, count,
    [], [], [], [], [], [], output, [], remaining, [], coefficientArray cs, depth, [], [], []]⟩

theorem pairProduct_embed (as bs cs : List IrreducibleSearch.F)
    (depth count remaining output newCount newRemaining newOutput : List Bool)
    (regs finalRegs : Fin 16 → Bool) :
    embedState id pairProductPorts (pairState as bs cs depth count remaining output regs)
      (productState as bs newCount newRemaining newOutput finalRegs) =
      pairState as bs cs depth newCount newRemaining newOutput finalRegs := by
  apply embedState_eq_of_ports id pairProductPorts _ _ _
    Function.injective_id pairProductPorts.injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h : 12 ≤ i.val := by
      by_contra hn
      exact hi ⟨⟨i.val, by omega⟩, rfl⟩
    fin_cases i <;> simp_all [pairState]

abbrev pairProductCall : Cmd 16 18 :=
  .call (ProgramLinking.liftProgram productProgram id pairProductPorts)

theorem pairProductCall_eval {d : ℕ} (a b : Fin d → IrreducibleSearch.F)
    (cs : List IrreducibleSearch.F) (depth remaining : List Bool) (regs : Fin 16 → Bool) :
    ∃ steps rf,
      steps ≤ remaining.length * (300 * (2 * d + remaining.length + 2) + 5) + 3 ∧
      Eval pairProductCall steps (pairState (List.ofFn a) (List.ofFn b) cs depth
        [false] remaining [] regs)
      (pairState (List.ofFn a) (List.ofFn b) cs depth
        (List.replicate remaining.length false ++ [false]) []
        (coefficientArray (((List.range remaining.length).map
          (IrreducibleSearch.convolution a b)).reverse)) rf) := by
  obtain ⟨rf, steps, hb, he⟩ := convolutionProduct_run a b remaining [] regs
  have ht := eval_call_lifted productProgram id pairProductPorts
    (pairState (List.ofFn a) (List.ofFn b) cs depth [false] remaining [] regs)
    Function.injective_id pairProductPorts.injective he
  simp only [List.append_nil] at ht
  rw [pairProduct_embed, pairProduct_embed] at ht
  exact ⟨steps, rf, hb, ht⟩

def pairProductSetupAtoms : List (Atom 16 18) :=
  [.set 14 false, .push 2 14, .push 11 14]
abbrev pairProductCommand : Cmd 16 18 :=
  .seq (copyCmd 14 11 17) <| .seq (copyCmd 14 11 17) <|
  .seq (.base (atomsCommand pairProductSetupAtoms)) <|
  .seq pairProductCall (clearCmd 2)

theorem pairProductCommand_eval {d : ℕ} (a b : Fin (d + 1) → IrreducibleSearch.F)
    (cs : List IrreducibleSearch.F) (depth : List Bool) (hlen : depth.length = d)
    (regs : Fin 16 → Bool) :
    ∃ steps rf, steps ≤ 10000 * (d + 1)^2 ∧
      Eval pairProductCommand steps (pairState (List.ofFn a) (List.ofFn b) cs depth [] [] [] regs)
        (pairState (List.ofFn a) (List.ofFn b) cs depth [] []
          (coefficientArray (((List.range (2*d+1)).map
            (IrreducibleSearch.convolution a b)).reverse)) rf) := by
  let d0 := pairState (List.ofFn a) (List.ofFn b) cs depth [] [] [] regs
  let d1 := copyState (14 : Fin 18) 11 d0
  let d2 := copyState (14 : Fin 18) 11 d1
  let d3 := atomsResult pairProductSetupAtoms d2
  have e1 := copy_eval (14 : Fin 18) 11 17 d0 (by decide) (by decide) (by decide)
    (by simp [d0, pairState])
  have e2 := copy_eval (14 : Fin 18) 11 17 d1 (by decide) (by decide) (by decide)
    (by simp [d1, d0, pairState, copyState, StackRoutines.copyStacks])
  have e3 := Eval.base (atoms_eval pairProductSetupAtoms d2)
  have h3 : d3 = pairState (List.ofFn a) (List.ofFn b) cs depth [false]
      (false :: (depth ++ depth)) [] d3.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i; fin_cases i <;>
      simp [d3, d2, d1, d0, atomsResult, pairProductSetupAtoms, pairState,
        copyState, StackRoutines.copyStacks, Atom.eval, Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
  obtain ⟨n, rf, hn, e4⟩ := pairProductCall_eval a b cs depth (false :: (depth ++ depth)) d3.regs
  rw [← h3] at e4
  have hr : (false :: (depth ++ depth)).length = 2*d+1 := by simp [hlen]; omega
  rw [hr] at e4 hn
  let d4 := pairState (List.ofFn a) (List.ofFn b) cs depth
    (List.replicate (2*d+1) false ++ [false]) []
    (coefficientArray (((List.range (2*d+1)).map
      (IrreducibleSearch.convolution a b)).reverse)) rf
  have e5 := clear_eval (2 : Fin 18) d4
  let d5 := clearState (2 : Fin 18) d4
  have h5 : d5 = pairState (List.ofFn a) (List.ofFn b) cs depth [] []
      (coefficientArray (((List.range (2*d+1)).map
        (IrreducibleSearch.convolution a b)).reverse)) d5.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i; fin_cases i <;> simp [d5, d4, clearState, pairState]
  have he := e1.seq (e2.seq (e3.seq (e4.seq e5)))
  change Eval pairProductCommand _ d0 d5 at he
  rw [h5] at he
  refine ⟨_, d5.regs, ?_, he⟩
  simp [d4, d1, d0, pairState, copyState, StackRoutines.copyStacks,
    pairProductSetupAtoms, hlen]
  nlinarith

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Candidate -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open SubexponentialSAT.StructuredProgram (Atom)

def candidatePorts : Fin 3 ↪ Fin 18 := ⟨![15, 5, 16], by decide⟩
def candidateCountAtoms : List (Atom 16 18) := [.set 14 false, .push 5 14]
abbrev candidateCommand : Cmd 16 18 :=
  .seq (copyCmd 13 15 17) <| .seq (appendOneCommand 15 3) <|
  .seq (copyCmd 14 5 17) <| .seq (copyCmd 14 5 17) <|
  .seq (.base (atomsCommand candidateCountAtoms)) (prefixCall sixRegisters candidatePorts)

def candidateState (as bs cs : List IrreducibleSearch.F)
    (depth product target : List Bool) (regs : Fin 16 → Bool) : State 16 18 :=
  ⟨regs, Function.update (pairState as bs cs depth [] [] product regs).stacks 16 target⟩

theorem candidateCommand_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (as bs : List IrreducibleSearch.F) (depth product : List Bool)
    (hlen : depth.length = d) (regs : Fin 16 → Bool) :
    ∃ steps rf, steps ≤ 100 * (d + 1) ∧
      Eval candidateCommand steps (pairState as bs (List.ofFn c) depth [] [] product regs)
        (candidateState as bs (List.ofFn c) depth product
          (coefficientArray (paddedPrefix (2*d+1) (List.ofFn c ++ [1])).reverse) rf) := by
  let d0 := pairState as bs (List.ofFn c) depth [] [] product regs
  let d1 := copyState (13 : Fin 18) 15 d0
  have e1 := copy_eval (13 : Fin 18) 15 17 d0 (by decide) (by decide) (by decide)
    (by simp [d0, pairState])
  obtain ⟨r2, e2⟩ := appendOneCommand_eval (15 : Fin 18) 3 (by decide) (List.ofFn c) d1
    (by simp [d1, d0, copyState, StackRoutines.copyStacks, pairState])
    (by simp [d1, d0, copyState, StackRoutines.copyStacks, pairState])
  let d2 : State 16 18 := ⟨r2, Function.update d1.stacks 15 (coefficientArray (List.ofFn c ++ [1]))⟩
  let d3 := copyState (14 : Fin 18) 5 d2
  let d4 := copyState (14 : Fin 18) 5 d3
  let d5 := atomsResult candidateCountAtoms d4
  have e3 := copy_eval (14 : Fin 18) 5 17 d2 (by decide) (by decide) (by decide)
    (by simp [d2, d1, d0, copyState, StackRoutines.copyStacks, pairState])
  have e4 := copy_eval (14 : Fin 18) 5 17 d3 (by decide) (by decide) (by decide)
    (by simp [d3, d2, d1, d0, copyState, StackRoutines.copyStacks, pairState])
  have e5 := Eval.base (atoms_eval candidateCountAtoms d4)
  obtain ⟨r6, e6⟩ := prefixCall_eval sixRegisters candidatePorts
    (List.ofFn c ++ [1]) (false :: (depth ++ depth)) [] d5
    (by simp [d5, d4, d3, d2, d1, d0, atomsResult, candidateCountAtoms,
      candidatePorts, copyState, StackRoutines.copyStacks, pairState, Atom.eval,
      Atom.instr, StructuredProgram.State.ofCfg, execInstr])
    (by simp [d5, d4, d3, d2, d1, d0, atomsResult, candidateCountAtoms,
      candidatePorts, copyState, StackRoutines.copyStacks, pairState, Atom.eval,
      Atom.instr, StructuredProgram.State.ofCfg, execInstr])
    (by simp [d5, d4, d3, d2, d1, d0, atomsResult, candidateCountAtoms,
      candidatePorts, copyState, StackRoutines.copyStacks, pairState, Atom.eval,
      Atom.instr, StructuredProgram.State.ofCfg, execInstr])
  have hc : (false :: (depth ++ depth)).length = 2*d+1 := by simp [hlen]; omega
  have hd : (List.ofFn c ++ [1]).drop (2*d+1) = [] := by
    apply List.drop_eq_nil_iff.mpr
    simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
    omega
  simp only [hc, hd, coefficientArray_nil, List.append_nil] at e6
  let d6 := afterThree sixRegisters candidatePorts r6 [] []
    (coefficientArray (paddedPrefix (2*d+1) (List.ofFn c ++ [1])).reverse) d5
  change Eval _ _ _ d6 at e6
  have h6 : d6 = candidateState as bs (List.ofFn c) depth product
      (coefficientArray (paddedPrefix (2*d+1) (List.ofFn c ++ [1])).reverse) d6.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i; fin_cases i <;>
      simp [d6, d5, d4, d3, d2, d1, d0, afterThree, replaceThree, candidatePorts,
        atomsResult, candidateCountAtoms, copyState, StackRoutines.copyStacks,
        candidateState, pairState, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  have he := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))
  change Eval candidateCommand _ d0 d6 at he
  rw [h6] at he
  refine ⟨_, d6.regs, ?_, he⟩
  simp [d3, d2, d1, d0, copyState, StackRoutines.copyStacks, pairState,
    coefficientArray_length, candidateCountAtoms, hlen]
  omega

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! ProductCheck -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def productComparePorts : Fin 2 ↪ Fin 18 := ⟨![9, 16], by decide⟩
abbrev productCheckCommand : Cmd 16 18 :=
  .seq pairProductCommand (.seq candidateCommand (compareCall productComparePorts))

theorem productCheckCommand_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (a b : Fin (d + 1) → IrreducibleSearch.F) (depth : List Bool)
    (hlen : depth.length = d) (regs : Fin 16 → Bool) :
    ∃ steps rf, steps ≤ 12000 * (d + 1)^2 ∧
      Eval productCheckCommand steps
        (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] regs)
        (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] rf) ∧
      rf 3 = IrreducibleSearch.productEq c a b := by
  let product := coefficientArray (((List.range (2*d+1)).map
    (IrreducibleSearch.convolution a b)).reverse)
  let target := coefficientArray (paddedPrefix (2*d+1) (List.ofFn c ++ [1])).reverse
  obtain ⟨n, r1, hn, e1⟩ := pairProductCommand_eval a b (List.ofFn c) depth hlen regs
  obtain ⟨m, r2, hm, e2⟩ := candidateCommand_eval c (List.ofFn a) (List.ofFn b)
    depth product hlen r1
  let d2 := candidateState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth product target r2
  have hlength : product.length = target.length := by
    simp [product, target, coefficientArray_length]
  obtain ⟨r3, e3, hv⟩ := compareCall_eval productComparePorts product target hlength d2
    (by simp [d2, candidateState, pairState, productComparePorts])
    (by simp [d2, candidateState, productComparePorts])
  let d3 := afterTwo fourRegisters productComparePorts r3 [] [] d2
  have h3 : d3 = pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] d3.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i; fin_cases i <;>
      simp [d3, d2, afterTwo, replaceTwo, productComparePorts, candidateState, pairState]
  have he := e1.seq (e2.seq e3)
  change Eval productCheckCommand _ _ d3 at he
  rw [h3] at he
  refine ⟨n + (m + (6 * product.length + 4)), d3.regs, ?_, he, ?_⟩
  · have hp : product.length = 2 * (2*d+1) := by simp [product, coefficientArray_length]
    rw [hp]
    have hsq : d + 1 ≤ (d + 1) ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_left (d + 1) (by omega)
    have hsmall : 100 * (d + 1) + 6 * (2 * (2 * d + 1)) + 4 ≤
        2000 * (d + 1) := by omega
    have hscale : 2000 * (d + 1) ≤ 2000 * (d + 1) ^ 2 :=
      Nat.mul_le_mul_left 2000 hsq
    omega
  · change d3.regs 3 = decide (product = target) at hv
    exact hv.trans (productComparison_eq c a b)

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Pair -/

/-! Closed primitive pair test. All three source vectors and the runtime
unary degree are preserved. The return bit is exactly the scalar pairPass. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open SubexponentialSAT.StructuredProgram (Atom)

def pairFlagsAtoms : List (Atom 16 18) :=
  [.pop 12 14 15, .band 3 14 3, .pop 12 14 15, .band 3 3 14, .bnot 3 3]

abbrev pairTailCommand : Cmd 16 18 :=
  .seq (.base (.atom (.push 12 3))) <| .seq (copyCmd 0 3 17) <|
  .seq (nonconstantCall 3) <| .seq (.base (.atom (.push 12 3))) <|
  .seq (copyCmd 1 3 17) <| .seq (nonconstantCall 3) (.base (atomsCommand pairFlagsAtoms))

theorem pairTailCommand_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (a b : Fin (d + 1) → IrreducibleSearch.F) (depth : List Bool) (regs : Fin 16 → Bool) :
    ∃ steps rf, steps ≤ 1000 * (d + 1) ∧
      Eval pairTailCommand steps
        (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] regs)
        (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] rf) ∧
      rf 3 = !(IrreducibleSearch.nonconstant a && IrreducibleSearch.nonconstant b && regs 3) := by
  let d0 := pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] regs
  let d1 := (Atom.push (12 : Fin 18) (3 : Fin 16)).eval d0
  let d2 := copyState (0 : Fin 18) 3 d1
  have e1 := Eval.base (StructuredProgram.Eval.atom (.push 12 3) d0)
  have e2 := copy_eval (0 : Fin 18) 3 17 d1 (by decide) (by decide) (by decide)
    (by simp [d1, d0, pairState, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr])
  obtain ⟨r3, e3, h3⟩ := nonconstantCall_eval (3 : Fin 18) a d2
    (by simp [d2, d1, d0, copyState, StackRoutines.copyStacks, pairState,
      Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr])
  let d3 := afterOne fourRegisters (3 : Fin 18) r3 [] d2
  let d4 := (Atom.push (12 : Fin 18) (3 : Fin 16)).eval d3
  let d5 := copyState (1 : Fin 18) 3 d4
  have e4 := Eval.base (StructuredProgram.Eval.atom (.push 12 3) d3)
  have e5 := copy_eval (1 : Fin 18) 3 17 d4 (by decide) (by decide) (by decide)
    (by simp [d4, d3, d2, d1, d0, afterOne, copyState, StackRoutines.copyStacks,
      pairState, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr])
  obtain ⟨r6, e6, h6⟩ := nonconstantCall_eval (3 : Fin 18) b d5
    (by simp [d5, d4, d3, d2, d1, d0, afterOne, copyState, StackRoutines.copyStacks,
      pairState, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr])
  let d6 := afterOne fourRegisters (3 : Fin 18) r6 [] d5
  let d7 := atomsResult pairFlagsAtoms d6
  have e7 := Eval.base (atoms_eval pairFlagsAtoms d6)
  have hs : d6.stacks 12 = [IrreducibleSearch.nonconstant a, regs 3] := by
    change d3.regs 3 = IrreducibleSearch.nonconstant a at h3
    simpa [d6, d5, d4, afterOne, copyState, StackRoutines.copyStacks,
      Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, StructuredProgram.State.withPC,
      execInstr, d3, d2, d1, d0, pairState] using h3
  have hv : d7.regs 3 =
      !(IrreducibleSearch.nonconstant a && IrreducibleSearch.nonconstant b && regs 3) := by
    change d6.regs 3 = IrreducibleSearch.nonconstant b at h6
    simp [d7, atomsResult, pairFlagsAtoms, Atom.eval, Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      readRegs, hs, h6]
  have hend : d7 = pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] d7.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i; fin_cases i <;>
      simp [d7, d6, d5, d4, d3, d2, d1, d0, atomsResult, pairFlagsAtoms,
        afterOne, copyState, StackRoutines.copyStacks, pairState, Atom.eval,
        Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  have he := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))
  change Eval pairTailCommand _ d0 d7 at he
  rw [hend] at he
  refine ⟨_, d7.regs, ?_, he, hv⟩
  simp [ d4, d3, d2, d1, d0, afterOne, copyState, StackRoutines.copyStacks,
    pairState, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr, coefficientArray_length, pairFlagsAtoms]
  omega

abbrev pairCommand : Cmd 16 18 := .seq productCheckCommand pairTailCommand

theorem pairCommand_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (a b : Fin (d + 1) → IrreducibleSearch.F) (depth : List Bool)
    (hlen : depth.length = d) (regs : Fin 16 → Bool) :
    ∃ steps rf, steps ≤ 14000 * (d + 1)^2 ∧
      Eval pairCommand steps
        (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] regs)
        (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] rf) ∧
      rf 3 = IrreducibleSearch.pairPass c (a, b) := by
  obtain ⟨n, r1, hn, e1, h1⟩ := productCheckCommand_eval c a b depth hlen regs
  obtain ⟨m, r2, hm, e2, h2⟩ := pairTailCommand_eval c a b depth r1
  refine ⟨n+m, r2, by nlinarith, e1.seq e2, ?_⟩
  simpa only [h1, IrreducibleSearch.pairPass] using h2

abbrev pairProgram : Program 16 18 (size pairCommand + 1) := compiled pairCommand 13 13

theorem pairProgram_run {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (a b : Fin (d + 1) → IrreducibleSearch.F) (depth : List Bool)
    (hlen : depth.length = d) (regs : Fin 16 → Bool) :
    ∃ rf, rf 3 = IrreducibleSearch.pairPass c (a,b) ∧
      RunsIn pairProgram (14000 * (d + 1)^2 + 1)
        ((pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] regs).withPC
          (some pairProgram.entry))
        ((pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] rf).withPC none) := by
  obtain ⟨n, rf, hn, he, hv⟩ := pairCommand_eval c a b depth hlen regs
  exact ⟨rf, hv, n+1, by omega, compiled_halt_trace he 13 13⟩


theorem pairProgram_primitive {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (a b : Fin (d + 1) → IrreducibleSearch.F) (depth : List Bool)
    (hlen : depth.length = d) (regs : Fin 16 → Bool) :
    ∃ rf, rf 3 = IrreducibleSearch.pairPass c (a,b) ∧
      Computation.RunsIn (primitive pairProgram).step
        (primitiveOverhead pairProgram * (14000 * (d + 1)^2 + 1))
        (primitiveCfg pairProgram
          ((pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] regs).withPC
            (some pairProgram.entry)))
        (primitiveCfg pairProgram
          ((pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] rf).withPC none)) := by
  obtain ⟨rf, hv, he⟩ := pairProgram_run c a b depth hlen regs
  exact ⟨rf, hv, BitProgram.primitive_execution pairProgram he⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
