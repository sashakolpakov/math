import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMomentProgram
import OAI.Algorithms.SubexponentialSAT.SubexpProjectedEvaluation

namespace OAI.Algorithms

/-!
# Parsing and evaluating one extraction job

This connects the actual three-frame job reader to the projected postfix
interpreter.  The only service assumptions concern traces of the installed
literal-projection and binary-arithmetic instruction tables.  In particular,
there is no assumed execution of the complete expression or job.
-/

namespace SubexponentialSAT.SubexpPreparedEvaluation

open BitProgram StructuredCalls
open SubexpMomentProgram (Job Data prepareJob preparedState)
open SubexpProjectedEvaluation
open SubexpEvaluationProgram (ecfg snapshot contextOf)

def preparationCost (j : Job) : ℕ :=
  9 * j.encode.length + 6 * (j.outputIndex.length + j.coefficientKey.length +
    j.sourceCode.length) + 9 * j.sourceCode.length + 26

abbrev command {a b c : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b)
    (loader : Program 16 128 c) : Cmd 16 128 :=
  .seq prepareJob (.call (readyEvaluationProgram add mul loader))

abbrev program {a b c : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b)
    (loader : Program 16 128 c) : Program 16 128 (size (command add mul loader) + 1) :=
  compiled (command add mul loader) 101 15

def resultState (before : Data) (bits : List Bool) : Data :=
  StructuredProgram.State.ofCfg (ecfg (l := 1) none false false false
    (snapshot bits (contextOf before.stacks)) [] [] [] bits)

theorem resultState_stacks (before : Data) (bits : List Bool) :
    (resultState before bits).stacks =
      Function.update (Function.update (Function.update (Function.update
        (Function.update before.stacks 26 []) 27 []) 28 []) 29 []) 15 bits := by
  funext i
  fin_cases i <;> rfl

theorem resultState_preserves (before : Data) (bits : List Bool) (i : Fin 128)
    (h15 : i ≠ 15) (h26 : i ≠ 26) (h27 : i ≠ 27) (h28 : i ≠ 28) (h29 : i ≠ 29) :
    (resultState before bits).stacks i = before.stacks i := by
  rw [resultState_stacks]
  simp [h15, h26, h27, h28, h29]

theorem resultState_fields (before : Data) (bits : List Bool) :
    (resultState before bits).stacks 15 = bits ∧
    (resultState before bits).stacks 26 = [] ∧
    (resultState before bits).stacks 27 = [] ∧
    (resultState before bits).stacks 28 = [] ∧
    (resultState before bits).stacks 29 = [] ∧
    (resultState before bits).regs = fun _ => false := by
  exact ⟨SubexpEvaluationProgram.evaluation_output (l := 1) bits (contextOf before.stacks),
    SubexpEvaluationProgram.evaluation_result_layout (l := 1) bits (contextOf before.stacks)⟩

theorem resultState_preserves_caller (before : Data) (bits : List Bool) (i : Fin 28) :
    (resultState before bits).stacks ⟨100 + i.val, by omega⟩ =
      before.stacks ⟨100 + i.val, by omega⟩ := by
  change (ecfg (l := 1) none false false false
    (snapshot bits (contextOf before.stacks)) [] [] [] bits).stacks _ = _
  rw [SubexpEvaluationProgram.evaluation_preserves_caller]
  fin_cases i <;> rfl

section Execution

variable {D : ℕ} {C : Type*} {a b c : ℕ}
variable (ops : SubexpSymbolicCost.RingProgram C)
  (slots : List (SymbolicCost.RawIndex D))
  (hslots : ∀ k ∈ slots, SymbolicCost.Retained D k)
  (add : Program 16 128 a) (mul : Program 16 128 b) (loader : Program 16 128 c)
  (encode : SymbolicCost.CoeffList D C → List Bool)
  (addBound mulBound : SymbolicCost.CoeffList D C → SymbolicCost.CoeffList D C → ℕ)
  (loadBound : SymbolicCost.CoeffList D C → ℕ)

def executionCost (base : Data) (j : Job)
    (e : Algorithm.Expr (SymbolicCost.CoeffList D C)) : ℕ :=
  preparationCost j +
    (operationCost (SubexpExecution.programOperations ops slots)
      encode addBound mulBound loadBound e +
      2 * ((contextOf (preparedState base j).stacks) 11).length +
      9 * (encode (SubexpExecution.programEval ops slots e).1).length + 35)

include hslots in
/-- Both parsing reversals, all three frame reads, the actual projected
postfix execution, and final result extraction occur in this trace. -/
theorem command_runs (base : Data) (j : Job)
    (e : Algorithm.Expr (SymbolicCost.CoeffList D C))
    (hsource : j.sourceCode = SubexpPostfixControl.serializeCode encode e.compile)
    (hs : base.stacks 101 = j.encode.reverse)
    (hi : base.stacks 103 = []) (hk : base.stacks 105 = []) (hc : base.stacks 26 = [])
    (h110 : base.stacks 110 = []) (h111 : base.stacks 111 = [])
    (h27 : base.stacks 27 = []) (h28 : base.stacks 28 = []) (h29 : base.stacks 29 = [])
    (ha : ImplementsOnGlobal RetainedList encode
      (fun x y => (SubexpSymbolicCost.programAdd ops slots x y).1)
      false add addBound (contextOf (preparedState base j).stacks))
    (hm : ImplementsOnGlobal RetainedList encode
      (fun x y => (SubexpSymbolicCost.programMul ops slots x y).1)
      true mul mulBound (contextOf (preparedState base j).stacks))
    (hl : LoadImplementsGlobal encode (fun x => (SubexpSymbolicCost.programProject ops slots x).1)
      loader loadBound (contextOf (preparedState base j).stacks)) :
    ∃ n ≤ executionCost ops slots encode addBound mulBound loadBound base j e,
      Eval (command add mul loader) n base
        (resultState (preparedState base j) (encode (SubexpExecution.programEval ops slots e).1)) := by
  have hp := SubexpMomentProgram.prepareJob_eval base j hs hi hk hc h110 h111
  have hf := SubexpMomentProgram.preparedState_fields base j hi hk hc
  have hcode : (preparedState base j).stacks 26 =
      SubexpPostfixControl.serializeCode encode e.compile := hf.2.2.2.trans hsource
  have h27' : (preparedState base j).stacks 27 = [] := by
    rw [SubexpMomentProgram.preparedState_preserves base j 27 (by decide) (by decide)
      (by decide) (by decide)]
    exact h27
  have h28' : (preparedState base j).stacks 28 = [] := by
    rw [SubexpMomentProgram.preparedState_preserves base j 28 (by decide) (by decide)
      (by decide) (by decide)]
    exact h28
  have h29' : (preparedState base j).stacks 29 = [] := by
    rw [SubexpMomentProgram.preparedState_preserves base j 29 (by decide) (by decide)
      (by decide) (by decide)]
    exact h29
  obtain ⟨n, hn, ht⟩ := ready_programEval_state_runsIn ops slots hslots add mul loader
    encode addBound mulBound loadBound e (preparedState base j).regs
    (preparedState base j).stacks hcode h27' h28' h29' ha hm hl
  have he : Eval (.call (readyEvaluationProgram add mul loader)) n (preparedState base j)
      (resultState (preparedState base j) (encode (SubexpExecution.programEval ops slots e).1)) := by
    apply Eval.call
    simpa only [resultState, StructuredProgram.State.ofCfg, StructuredProgram.State.withPC] using ht
  exact ⟨preparationCost j + n, Nat.add_le_add_left hn _, Eval.seq hp he⟩

/-- The parsed output index and coefficient key remain available to the next
lookup/update stage, while the dense value is on its agreed output port. -/
theorem output_layout (base : Data) (j : Job) (bits : List Bool)
    (hi : base.stacks 103 = []) (hk : base.stacks 105 = []) (hc : base.stacks 26 = []) :
    let out := resultState (preparedState base j) bits
    out.stacks 15 = bits ∧ out.stacks 103 = j.outputIndex.reverse ∧
      out.stacks 105 = j.coefficientKey.reverse ∧ out.stacks 101 = [] ∧
      out.stacks 100 = base.stacks 100 ∧ out.stacks 102 = base.stacks 102 := by
  dsimp only
  have h := SubexpMomentProgram.preparedState_fields base j hi hk hc
  have h100 := resultState_preserves_caller (preparedState base j) bits (0 : Fin 28)
  have h101 := resultState_preserves_caller (preparedState base j) bits (1 : Fin 28)
  have h102 := resultState_preserves_caller (preparedState base j) bits (2 : Fin 28)
  have h103 := resultState_preserves_caller (preparedState base j) bits (3 : Fin 28)
  have h105 := resultState_preserves_caller (preparedState base j) bits (5 : Fin 28)
  refine ⟨(resultState_fields _ _).1, h103.trans h.2.1, h105.trans h.2.2.1,
    h101.trans h.1, ?_, ?_⟩
  · exact h100.trans (SubexpMomentProgram.preparedState_preserves base j 100
      (by decide) (by decide) (by decide) (by decide))
  · exact h102.trans (SubexpMomentProgram.preparedState_preserves base j 102
      (by decide) (by decide) (by decide) (by decide))

end Execution

theorem program_trace {a b c n : ℕ} (add : Program 16 128 a)
    (mul : Program 16 128 b) (loader : Program 16 128 c) {before after : Data}
    (h : Eval (command add mul loader) n before after) :
    Trace (program add mul loader) (n + 1)
      (before.withPC (some (program add mul loader).entry)) (after.withPC none) :=
  compiled_halt_trace h 101 15

theorem primitive_execution {a b c n bound : ℕ} (add : Program 16 128 a)
    (mul : Program 16 128 b) (loader : Program 16 128 c) {before after : Data}
    (h : Eval (command add mul loader) n before after) (hn : n ≤ bound) :
    Computation.RunsIn (primitive (program add mul loader)).step
      (primitiveOverhead (program add mul loader) * (bound + 1))
      (primitiveCfg (program add mul loader)
        (before.withPC (some (program add mul loader).entry)))
      (primitiveCfg (program add mul loader) (after.withPC none)) := by
  obtain ⟨steps, hs, ht⟩ := primitive_trace _ (program_trace add mul loader h)
  exact ⟨steps, hs.trans (Nat.mul_le_mul_left _ (by omega)), ht⟩

end SubexponentialSAT.SubexpPreparedEvaluation

end OAI.Algorithms
