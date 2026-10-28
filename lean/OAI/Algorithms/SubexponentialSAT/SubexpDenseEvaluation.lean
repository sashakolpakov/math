import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseMultiplication

namespace OAI.Algorithms

/-!
# The concrete dense polynomial evaluator

All three arithmetic service tables are fixed here. The hypotheses describe
the actual metadata and scratch stacks, canonical zero, scalar width and
retained output slots; no arithmetic execution callback is assumed.
-/

namespace SubexponentialSAT.SubexpDenseEvaluation

open BitProgram SymbolicCost SubexpSymbolicCost SubexpLiftRing SubexpQuarticRing
open SubexpCanonicalWords SubexpDenseSerialization SubexpDenseOperands
open SubexpEvaluationProgram (contextOf ecfg snapshot)

/-- Exactly the physical stack ports inspected by the arithmetic context. -/
def MetadataPort (i : Fin 128) : Prop :=
  i.val < 26 ∨ (30 ≤ i.val ∧ i.val < 100)

theorem contextOf_stack (stk : Fin 128 → List Bool) (i : Fin 128)
    (h26 : i ≠ 26) (h27 : i ≠ 27) (h28 : i ≠ 28) (h29 : i ≠ 29) :
    (physicalState false false false [] [] [] (contextOf stk)).stacks i = stk i := by
  obtain ⟨j, rfl⟩ := SubexpPostfixGlobal.ports.surjective i
  revert h26 h27 h28 h29
  refine Fin.addCases (m := 4) (n := 124) (fun j => ?_) (fun j => ?_) j
  · fin_cases j <;> simp
  · intro _ _ _ _
    simp only [physicalState, StructuredProgram.State.ofCfg,
      SubexpPostfixGlobal.physicalCfg_context, contextOf]

theorem contextOf_metadata (stk : Fin 128 → List Bool) (i : Fin 128)
    (hi : MetadataPort i) :
    (physicalState false false false [] [] [] (contextOf stk)).stacks i = stk i := by
  apply contextOf_stack
  all_goals intro he; subst i; norm_num [MetadataPort, Fin.coe_ofNat_eq_mod] at hi

/-- Preparation may freely change code, operand/depth ports and all ports
100 and above. Only equality on the actual metadata ports is needed. -/
theorem contextReady_of_metadata {stk stk' : Fin 128 → List Bool}
    {modulus width master reduction keyWidth : List Bool}
    (h : SubexpDenseMultiplication.ContextReady (contextOf stk)
      modulus width master reduction keyWidth)
    (heq : ∀ i, MetadataPort i → stk' i = stk i) :
    SubexpDenseMultiplication.ContextReady (contextOf stk')
      modulus width master reduction keyWidth := by
  have he (i : Fin 128) (hi : MetadataPort i) :
      (physicalState false false false [] [] [] (contextOf stk')).stacks i =
        (physicalState false false false [] [] [] (contextOf stk)).stacks i := by
    rw [contextOf_metadata _ _ hi, contextOf_metadata _ _ hi, heq i hi]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [he (SubexpDenseOperandWrappers.coreStacks i) (Or.inl (by exact i.isLt))]
    exact h.core i
  · intro i hlo hhi
    rw [he i (Or.inr ⟨hlo, by omega⟩)]
    exact h.bank i hlo hhi
  · rw [he 91 (by norm_num [MetadataPort, Fin.coe_ofNat_eq_mod])]
    exact h.reduction
  · rw [he 92 (by norm_num [MetadataPort, Fin.coe_ofNat_eq_mod])]
    exact h.keyWidth
  · intro i hlo hhi
    rw [he i (Or.inr ⟨by omega, hhi⟩)]
    exact h.scratch i hlo hhi

theorem contextReady_output_empty {context : Fin 124 → List Bool}
    {modulus width master reduction keyWidth : List Bool}
    (h : SubexpDenseMultiplication.ContextReady context
      modulus width master reduction keyWidth) : context 11 = [] := by
  exact h.core.empty 15 (by decide) (by decide) (by decide)

def program := SubexpProjectedEvaluation.readyEvaluationProgram
  SubexpDenseOperands.addService SubexpDenseMultiplication.service SubexpDenseOperands.loadService

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D+1))
  (t z o : QuarticCode p D) (slots : List (RawIndex D))

def cost (e : Algorithm.Expr (CoeffList D (QuarticCode p D))) : ℕ :=
  SubexpProjectedEvaluation.operationCost
    (SubexpExecution.programOperations (preparedProgram p D M t z o) slots)
    (encodeFixedQuarticCoefficients p D)
    (SubexpDenseOperands.addBound p D M t z o slots)
    (SubexpDenseMultiplication.bound p D M t z o slots)
    (SubexpDenseOperands.loadBound p D M t z o slots) e +
  9 * (encodeFixedQuarticCoefficients p D
    (SubexpExecution.programEval (preparedProgram p D M t z o) slots e).1).length + 35

variable (c : Fin 4 → ZMod (p^(D+1)))
  (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
  (hcanonical : CanonicalQuad p (D+1) z)
  (width : List Bool) (hwidth : width.length = baseWidth p (D+1))

include hz hcanonical hwidth

/-- Common metadata supplies all three concrete local service contracts.
Literal projection accepts unrestricted raw coefficient lists. -/
theorem contracts (context : Fin 124 → List Bool)
    (hcontext : SubexpDenseMultiplication.ContextReady context M.bits width
      (SubexpDenseProgram.Projection.queryBytes slots) (SubexpQuarticFlatMul.flat t)
      (List.replicate (indexBits D) true)) :
    SubexpProjectedEvaluation.ImplementsOnGlobal SubexpProjectedEvaluation.RetainedList
      (encodeFixedQuarticCoefficients p D)
      (fun P Q => (programAdd (preparedProgram p D M t z o) slots P Q).1)
      false SubexpDenseOperands.addService (SubexpDenseOperands.addBound p D M t z o slots) context ∧
    SubexpProjectedEvaluation.ImplementsOnGlobal SubexpProjectedEvaluation.RetainedList
      (encodeFixedQuarticCoefficients p D)
      (fun P Q => (programMul (preparedProgram p D M t z o) slots P Q).1)
      true SubexpDenseMultiplication.service (SubexpDenseMultiplication.bound p D M t z o slots) context ∧
    SubexpProjectedEvaluation.LoadImplementsGlobal
      (encodeFixedQuarticCoefficients p D)
      (fun P => (programProject (preparedProgram p D M t z o) slots P).1)
      SubexpDenseOperands.loadService (SubexpDenseOperands.loadBound p D M t z o slots) context := by
  exact ⟨SubexpDenseOperands.add_implements p D M t z o slots c hz hcanonical
      width hwidth context hcontext.core,
    SubexpDenseMultiplication.implements p D M t z o slots c hz hcanonical
      width hwidth context hcontext,
    SubexpDenseOperands.load_implements p D M t z o slots c hz hcanonical
      width hwidth context hcontext.core⟩

/-- Execution of the fixed evaluator on the actual serialized raw expression.
All arithmetic service executions are discharged by concrete programs. -/
theorem ready_programEval_state_runsIn
    (hslots : ∀ a ∈ slots, Retained D a)
    (e : Algorithm.Expr (CoeffList D (QuarticCode p D)))
    (regs : Fin 16 → Bool) (stk : Fin 128 → List Bool)
    (h26 : stk 26 = SubexpPostfixControl.serializeCode
      (encodeFixedQuarticCoefficients p D) e.compile)
    (h27 : stk 27 = []) (h28 : stk 28 = []) (h29 : stk 29 = [])
    (hcontext : SubexpDenseMultiplication.ContextReady (contextOf stk) M.bits width
      (SubexpDenseProgram.Projection.queryBytes slots) (SubexpQuarticFlatMul.flat t)
      (List.replicate (indexBits D) true)) :
    RunsIn program (cost p D M t z o slots e)
      ⟨some program.entry, regs, stk⟩
      (ecfg none false false false
        (snapshot (encodeFixedQuarticCoefficients p D
          (SubexpExecution.programEval (preparedProgram p D M t z o) slots e).1) (contextOf stk))
        [] [] [] (encodeFixedQuarticCoefficients p D
          (SubexpExecution.programEval (preparedProgram p D M t z o) slots e).1)) := by
  obtain ⟨ha, hm, hl⟩ := contracts p D M t z o slots c hz hcanonical width hwidth
    (contextOf stk) hcontext
  have h := SubexpProjectedEvaluation.ready_programEval_state_runsIn
    (preparedProgram p D M t z o) slots hslots
    SubexpDenseOperands.addService SubexpDenseMultiplication.service SubexpDenseOperands.loadService
    (encodeFixedQuarticCoefficients p D)
    (SubexpDenseOperands.addBound p D M t z o slots)
    (SubexpDenseMultiplication.bound p D M t z o slots)
    (SubexpDenseOperands.loadBound p D M t z o slots)
    e regs stk h26 h27 h28 h29 ha hm hl
  simpa only [program, cost, contextReady_output_empty hcontext, List.length_nil,
    Nat.mul_zero, Nat.add_zero] using h

end SubexponentialSAT.SubexpDenseEvaluation

end OAI.Algorithms
