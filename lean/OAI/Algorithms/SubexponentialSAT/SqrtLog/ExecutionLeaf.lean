import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionController

namespace OAI.Algorithms

/-!
# One-procedure leaf adapter

The new sparse-code/hash/evaluator leaf is one actual finite procedure. The
adapter supplies the already implemented payload transfer and final cleanup;
it does not require the old layout/moments/CRT/decode decomposition.
-/

namespace SubexponentialSAT.SqrtLog.Execution

open SubexpMainProgram StructuredCalls

variable {er es : ℕ}

def singleLeaf (body : Procedure er es) : MainCmd er es :=
  .seq (transferLeaf er es) (.seq body.invoke (finishLeaf er es))

/-- The only operation supplied by a body implementation is a measured
execution of its fixed finite program from the actual transferred input. -/
structure LeafBodyRun (body : Procedure er es) (start : MainState er es) where
  afterBody : MainState er es
  bodySteps : ℕ
  bodyTrace : Eval body.invoke bodySteps (transferredData start) afterBody

def LeafBodyRun.steps {body : Procedure er es} {start : MainState er es}
    (run : LeafBodyRun body start) : ℕ :=
  transferCost start + (run.bodySteps + finishCost run.afterBody)

theorem LeafBodyRun.execution {body : Procedure er es} {start : MainState er es}
    (run : LeafBodyRun body start) :
    Eval (singleLeaf body) run.steps start (finishedData run.afterBody) :=
  .seq (transferLeaf_eval start) (.seq run.bodyTrace (finishLeaf_eval run.afterBody))

/-- All obligations for the real leaf body, including restoration of the
unread source and the reusable invariant. `test` is specification only;
its bit must actually be written by the body on persistent stack10. -/
def LeafBodyContract (body : Procedure er es) (test : List Bool → Bool)
    (cost : List Bool → ℕ) (invariant : MainState er es → Prop)
    (validPayload : List Bool → Prop) : Prop :=
  ∀ (bits tail : List Bool) (base : MainState er es),
    validPayload bits → invariant base →
    ∃ run : LeafBodyRun body (leafInput base tail bits),
      run.steps ≤ cost bits ∧ invariant (finishedData run.afterBody) ∧
      run.afterBody.stacks (persistent es 7) = tail ∧
      run.afterBody.stacks (persistent es 8) = [] ∧
      (run.afterBody.stacks (persistent es 10)).head? = some (test bits)

/-- Plugging this theorem into CanonicalCertificate.run.callback or
OrderedCertificate.run.callback links the single body to the actual parser. -/
theorem singleLeaf_contract {body : Procedure er es} {test : List Bool → Bool}
    {cost : List Bool → ℕ} {invariant : MainState er es → Prop}
    {validPayload : List Bool → Prop}
    (contract : LeafBodyContract body test cost invariant validPayload) :
    RecordPrograms.CallbackContractOn (ports er es) (singleLeaf body)
      test cost invariant validPayload := by
  intro bits tail base hv hi
  obtain ⟨run, hn, hinv, hs, hp, ha⟩ := contract bits tail base hv hi
  refine ⟨run.steps, finishedData run.afterBody, hn, hinv, ?_⟩
  have he := run.execution
  rw [finished_record_state run.afterBody tail (test bits) hs hp ha] at he
  exact he

end SubexponentialSAT.SqrtLog.Execution

end OAI.Algorithms
