import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparsifyProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupBanks
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawSparsify

namespace OAI.Algorithms

/-! Transport the actual new-schedule bank producer through the actual Main
normalizer and register reset into the physical splitter frame. -/
namespace SubexponentialSAT.SqrtLog.SparsifyProgram.Main

open BitProgram StructuredCalls SubexpSetupProgram
open SubexpMainProgram (MainState workRegs persistent)
open ExecSparsifyWorklist (normalizedInput)
open ExecSparsifyObserved (encode)

/-- Postconditions on the physical Main state. Word lengths refer to the
producer's padded words, not to re-encoded numerical values. -/
structure Prepared (c : Config) {er : ℕ} (n : ℕ)
    (a : MainState er (mainExtraStacks c)) : Prop where
  clean : SubexpNormalizedSparsify.EmptyPrefix (helperSize c) a
  bank : ∀ i : Fin (thresholdCount c), BinaryArithmetic.toNat
    (a.stacks (mainStack c (SubexpSetupProgram.threshold c i))) = arity c.T n (i.val + 2)
  lengths : ∀ i : Fin (thresholdCount c),
    (a.stacks (mainStack c (SubexpSetupProgram.threshold c i))).length ≤
      ArithmeticExpressionProgram.widthCoeff
        (SparsificationThresholdProgram.thresholdExpr (i.val + 2)) *
          ((SparsificationBudgetProgram.outputWord c.T (Asymptotic.s n)).length + 1)

/-- The producer's actual installation, using its existing injective stack
map, supplies every splitter-preparation premise. -/
theorem prepared_install (c : Config) {er n : ℕ}
    (a : MainState er (mainExtraStacks c)) (out : SetupState c)
    (hv : Setup.Banks.Values c (Asymptotic.s n) out) :
    Prepared c n ((Setup.Banks.procedure c er).install a out) := by
  have hstack (i : Fin (stackCount c)) :
      ((Setup.Banks.procedure c er).install a out).stacks (mainStack c i) = out.stacks i := by
    exact embedState_stack (Setup.Banks.procedure c er).registerMap
      (Setup.Banks.procedure c er).stack a out (Setup.Banks.procedure c er).stack.injective i
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    let j : Fin (stackCount c) := Fin.cast (main_stackCount c).symm i
    have hj : mainStack c j = i := Fin.ext rfl
    rw [← hj, hstack]
    exact hv.clean j hi
  · intro i
    rw [hstack]
    exact hv.threshold i
  · intro i
    rw [hstack]
    exact hv.lengths i

/-- A convenient alias for the exact frame consumed by the old Main
procedure, now parameterized by the new schedule. -/
noncomputable def localFrame (c : Config) {er n : ℕ} (hr : 32 ≤ workRegs er)
    (F : ExecSparsifyObserved.Formula n) (middle : MainState er (mainExtraStacks c)) :=
  SubexpConcreteNode.localFrame c hr (SubexpOrderedRawSparsify.inputFrame c hr F middle)

/-- Any actual normalizer run preserves the producer bank and its lengths.
The work-register reset is part of the existing physical input frame. -/
theorem normalized_frame (c : Config) {er n t : ℕ} (hr : 32 ≤ workRegs er)
    (F : ExecSparsifyObserved.Formula n)
    {caller middle : MainState er (mainExtraStacks c)} (hp : Prepared c n caller)
    (hbody : caller.stacks (persistent (mainExtraStacks c) 0) = encode F)
    (he : Eval (SubexpMainNormalization.procedure er (mainExtraStacks c)).invoke t caller middle) :
    ExecSparsifyBoundary.FrameReady (localFrame c hr F middle) ∧
    ExecSparsifyObserved.BankValues (arity c.T n) (localFrame c hr F middle) ∧
    BankLengths c.k c.T n (localFrame c hr F middle) := by
  let G := F.map (List.map Encoding.literalCode)
  have hbody' : caller.stacks (persistent (mainExtraStacks c) 0) =
      SubexpNormalizationProgram.formulaCode G :=
    hbody.trans (SubexpOrderedRawSparsify.body_code F).symm
  obtain ⟨hc, ht, _⟩ := SubexpSparsifyInput.normalization_post c G hbody' hp.clean he
  have hframe (i : Fin (thresholdCount c)) :
      (SubexpOrderedRawSparsify.inputFrame c hr F middle).stacks
          (mainStack c (SubexpSetupProgram.threshold c i)) = caller.stacks (mainStack c (SubexpSetupProgram.threshold c i)) :=
    (SubexpSparsifyInput.inputFrame_threshold c (SubexpConcreteNode.program c hr)
      middle (encode (normalizedInput F)) i).trans (ht i)
  refine ⟨SubexpConcreteNode.local_ready c hr _
    (SubexpSparsifyInput.inputFrame_ready c (SubexpConcreteNode.program c hr)
      middle (encode (normalizedInput F)) hc), ?_, ?_⟩
  · apply SubexpConcreteNode.local_bank c hr
    intro i
    rw [hframe i]
    exact hp.bank i
  · intro i
    rw [SubexpConcreteNode.search_threshold_eq]
    change ((SubexpConcreteNode.localFrame c hr
      (SubexpOrderedRawSparsify.inputFrame c hr F middle)).stacks
        (SubexpNodePorts.thresholdPort c.k i)).length ≤ _
    have heq : (SubexpConcreteNode.localFrame c hr
        (SubexpOrderedRawSparsify.inputFrame c hr F middle)).stacks
        (SubexpNodePorts.thresholdPort c.k i) =
        caller.stacks (mainStack c (SubexpSetupProgram.threshold c i)) :=
      (SubexpNodeRealization.setup_project_threshold c hr _ i).trans (hframe i)
    rw [heq]
    exact hp.lengths i

end SubexponentialSAT.SqrtLog.SparsifyProgram.Main

end OAI.Algorithms
