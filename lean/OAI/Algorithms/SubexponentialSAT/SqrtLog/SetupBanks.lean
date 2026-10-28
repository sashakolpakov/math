import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticSchedule
import OAI.Algorithms.SubexponentialSAT.SubexpSetupPhaseArithmetic
import OAI.Algorithms.SubexponentialSAT.SubexpSetupPhaseTable
import OAI.Algorithms.SubexponentialSAT.SubexpSetupControl
import OAI.Algorithms.SubexponentialSAT.SubexpSetupInvariant
import OAI.Algorithms.SubexponentialSAT.SubexpSetupProcedure

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Banks

open BitProgram StructuredCalls BinaryArithmetic
open SubexpSetupProgram SubexpSetupStorage SubexpSetupPhaseArithmetic SubexpSetupPhaseTable

/-- The existing physical stages are parameterized by the new word on slot4;
none of the old schedule-specific scalar setup theorem is used. -/
def command (c : Config) : SetupCmd c :=
  .seq (selectM c) (.seq (occurrence c)
    (.seq (thresholdTable c) (clearMany (workspacePorts c))))

def program (c : Config) := compiled (command c) (persistent c 0) (persistent c 0)

structure Values (c : Config) (s : ℕ) (b : SetupState c) : Prop where
  Mword : b.stacks (persistent c 23) = SparsificationBudgetProgram.outputWord c.T s
  Mvalue : BinaryArithmetic.toNat (b.stacks (persistent c 23)) = SparsificationBudgetProgram.dyadicM c.T s
  occurrence : BinaryArithmetic.toNat (b.stacks (persistent c 24)) =
    SparsificationConstants.occurrenceCap (SparsificationBudgetProgram.dyadicM c.T s) c.k
  threshold : ∀ i : Fin (thresholdCount c), BinaryArithmetic.toNat (b.stacks (SubexpSetupProgram.threshold c i)) =
    SparsificationConstants.z (SparsificationBudgetProgram.dyadicM c.T s) (i.val+2)
  lengths : ∀ i : Fin (thresholdCount c), (b.stacks (SubexpSetupProgram.threshold c i)).length ≤
    ArithmeticExpressionProgram.widthCoeff (SparsificationThresholdProgram.thresholdExpr (i.val+2)) *
      ((SparsificationBudgetProgram.outputWord c.T s).length+1)
  clean : ∀ i : Fin (stackCount c), i.val < helperSize c → b.stacks i = []

theorem command_eval (c : Config) (a : SetupState c) :
    ∃ t b, Eval (command c) t a b ∧ Values c (BinaryArithmetic.toNat (a.stacks (persistent c 4))) b ∧
      (∀ i : Fin 32, i ≠ 23 → i ≠ 24 → b.stacks (persistent c i) = a.stacks (persistent c i)) := by
  obtain ⟨t1,_,h1,hM,_,hf1⟩ := selectM_eval c a
  let a1 := selectResult c a
  have hwM : a1.stacks (persistent c 23) =
      SparsificationBudgetProgram.outputWord c.T (BinaryArithmetic.toNat (a.stacks (persistent c 4))) :=
    selectResult_word c a
  obtain ⟨t2,r2,w2,_,h2,hOcc,_,hf2⟩ := occurrence_eval c a1
  let a2 := occurrenceResult c a1 r2 w2
  have hf2M : a2.stacks (persistent c 23) = a1.stacks (persistent c 23) :=
    hf2.2 _ (persistent_protected c 23) (by simp)
  obtain ⟨t3,r3,w3,_,h3,hT,_,_⟩ := table_eval c a2
  let a3 := tableResult c a2 r3 w3
  have hf3 : ∀ i : Fin 32, a3.stacks (persistent c i) = a2.stacks (persistent c i) :=
    table_result_persistent c a2 r3 w3
  obtain ⟨h4,hf4,hclean⟩ := workspace_cleanup c a3
  let b := clearManyState (workspacePorts c) a3
  have hf4P (i : Fin 32) : b.stacks (persistent c i) = a3.stacks (persistent c i) :=
    hf4.2 _ (persistent_protected c i) (by simp)
  have hf4T (i : Fin (thresholdCount c)) : b.stacks (SubexpSetupProgram.threshold c i) =
      a3.stacks (SubexpSetupProgram.threshold c i) :=
    hf4.2 _ (threshold_protected c i) (by simp)
  refine ⟨_,b,h1.seq (h2.seq (h3.seq h4)),?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_,hclean⟩
    · rw [hf4P,hf3,hf2M,hwM]
    · rw [hf4P,hf3,hf2M]
      exact hM
    · rw [hf4P,hf3,hOcc,hM]
    · intro i
      rw [hf4T]
      exact (hT i).1.trans (by rw [hf2M,hM])
    · intro i
      rw [hf4T]
      have hi := (hT i).2
      rwa [hf2M,hwM] at hi
  · intro i hi23 hi24
    rw [hf4P,hf3]
    rw [hf2.2 _ (persistent_protected c i) (by simpa using hi24)]
    exact hf1.2 _ (persistent_protected c i) (by simpa using hi23)

/-- Specialization to the proved new integer schedule. -/
theorem scheduled_eval (c : Config) (n : ℕ) (a : SetupState c)
    (hs : BinaryArithmetic.toNat (a.stacks (persistent c 4)) = Asymptotic.s n) :
    ∃ t b, Eval (command c) t a b ∧ Values c (Asymptotic.s n) b ∧
      (∀ i : Fin 32, i ≠ 23 → i ≠ 24 → b.stacks (persistent c i) = a.stacks (persistent c i)) := by
  simpa only [hs] using command_eval c a

/-- The same physical Main layout used by the existing splitter. -/
def procedure (c : Config) (er : ℕ) :
    SubexpMainProgram.Procedure er (mainExtraStacks c) where
  registers := 16
  stackCount := stackCount c
  labels := size (command c) + 1
  program := program c
  register := (mainProcedure c er).register
  stack := (mainProcedure c er).stack

theorem procedure_eval (c : Config) (er n : ℕ)
    (a : SubexpMainProgram.MainState er (mainExtraStacks c))
    (hs : BinaryArithmetic.toNat (a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 4)) = Asymptotic.s n) :
    ∃ t out, Eval (procedure c er).invoke t a ((procedure c er).install a out) ∧
      Values c (Asymptotic.s n) out ∧
      (∀ i : Fin 32, i ≠ 23 → i ≠ 24 →
        ((procedure c er).install a out).stacks
          (SubexpMainProgram.persistent (mainExtraStacks c) i) =
        a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) i)) := by
  let localState := (procedure c er).project a
  have hlocal : BinaryArithmetic.toNat (localState.stacks (persistent c 4)) = Asymptotic.s n := by
    change BinaryArithmetic.toNat (a.stacks (mainStack c (persistent c 4))) = _
    simpa only [mainStack_persistent] using hs
  obtain ⟨t,out,he,hv,hf⟩ := scheduled_eval c n localState hlocal
  refine ⟨t+1,out,(procedure c er).invoke_trace a out (compiled_halt_trace he _ _),hv,?_⟩
  intro i hi23 hi24
  rw [← mainStack_persistent c i]
  have hout := embedState_stack (procedure c er).registerMap (procedure c er).stack a out
    (procedure c er).stack.injective (persistent c i)
  change ((procedure c er).install a out).stacks (mainStack c (persistent c i)) = _ at hout
  rw [hout,hf i hi23 hi24]
  rfl

end SubexponentialSAT.SqrtLog.Setup.Banks

end OAI.Algorithms
