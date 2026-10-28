import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupExecution
import OAI.Algorithms.SubexponentialSAT.SubexpSetupProcedure

namespace OAI.Algorithms

/-! The closed numerical setup supplies a real Main-program phase trace. -/

namespace SubexponentialSAT.SubexpSetupProgram

open BitProgram StructuredCalls SubexpMainProgram

/-- The width-dependent control and workspace are chosen before any input. -/
theorem config_exists (k extra : ℕ) (hk : 2 ≤ k) :
    ∃ c : Config, c.k = k ∧ c.extra = extra := by
  obtain ⟨T, hT⟩ := SparsificationBudgetProgram.exists_control k
  exact ⟨⟨k, T, extra, hk, hT⟩, rfl, rfl⟩

theorem main_project_word (c : Config) (er : ℕ) (a : MainState er (mainExtraStacks c))
    (i : Fin 32) :
    ((mainProcedure c er).project a).stacks (persistent c i) =
      a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) i) := by
  change a.stacks (mainStack c (persistent c i)) = _
  rw [mainStack_persistent]

theorem main_install_word (c : Config) (er : ℕ) (a : MainState er (mainExtraStacks c))
    (out : SetupState c) (i : Fin 32) :
    ((mainProcedure c er).install a out).stacks
      (SubexpMainProgram.persistent (mainExtraStacks c) i) = out.stacks (persistent c i) := by
  rw [← mainStack_persistent c i]
  exact embedState_stack _ _ _ _ (mainProcedure c er).stack.injective (persistent c i)

theorem main_install_flag (c : Config) (er : ℕ) (a : MainState er (mainExtraStacks c))
    (out : SetupState c) :
    ((mainProcedure c er).install a out).regs ((mainProcedure c er).registerMap (15 : Fin 16)) = out.regs 15 :=
  embedState_register _ _ _ _ (mainProcedure c er).registerMap_injective (15 : Fin 16)

private theorem prefix_word (er es : ℕ) (input body nb sb ub : List Bool) (i : Fin 6) :
    (prefixData er es input body nb sb ub).stacks
      (SubexpMainProgram.persistent es (i.castAdd 26)) =
      (SubexpFrontendPrefix.state body nb sb ub).stacks i :=
  embedState_stack _ _ _ _ (frontendProcedure er es).stack.injective i

/-- The only input hypotheses are the binary words already produced by the
actual raw frontend. The numerical phase and its outputs are proved here. -/
theorem main_execution (c : Config) (er n : ℕ) (a : MainState er (mainExtraStacks c))
    (hn : BinaryArithmetic.toNat (a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 2)) = n)
    (hs : BinaryArithmetic.toNat (a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 4)) =
      SubexpPackingParameters.s n)
    (hu : BinaryArithmetic.toNat (a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 5)) =
      SubexpPackingParameters.u n) :
    ∃ t out, Eval (mainProcedure c er).invoke t a ((mainProcedure c er).install a out) ∧
      (((mainProcedure c er).install a out).regs ((mainProcedure c er).registerMap (15 : Fin 16)) = true ↔
        DyadicSchedule.Ready c.k c.T n) ∧
      (SubexpPackingParameters.GoodInput n → ScalarValues c n out ∧ ThresholdValues c n out) ∧
      (∀ i : Fin 32, Retained i →
        ((mainProcedure c er).install a out).stacks
          (SubexpMainProgram.persistent (mainExtraStacks c) i) =
        a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) i)) ∧
      (∀ i : Fin (stackCount c), i.val < helperSize c →
        ((mainProcedure c er).install a out).stacks (mainStack c i) = []) := by
  have hk : Known c n initialKnown ((mainProcedure c er).project a) := by
    apply initialKnown_of_words c n _
    · rw [main_project_word]; exact hn
    · rw [main_project_word]; exact hs
    · rw [main_project_word]; exact hu
  obtain ⟨t, out, ht, hv, hvalues, hp, hw⟩ :=
    program_execution c n ((mainProcedure c er).project a) hk
  refine ⟨t, out, (mainProcedure c er).invoke_trace a out ht, ?_, hvalues, ?_, ?_⟩
  · rw [main_install_flag]
    exact hv
  · intro i hi
    rw [main_install_word, hp i hi, main_project_word]
  · intro i hi
    exact (embedState_stack _ _ _ _ (mainProcedure c er).stack.injective i).trans (hw i hi)

/-- Starting from the raw formula, the real frontend supplies all inputs to
the setup phase. This statement has no encoded-parameter hypotheses. -/
theorem raw_execution (c : Config) (er : ℕ) {n : ℕ} (F : SAT.CNF (Fin n)) :
    ∃ (prefixSteps setupSteps : ℕ) (before : MainState er (mainExtraStacks c))
      (out : SetupState c),
      prefixSteps ≤ SubexpFrontendPrefix.bound (Encoding.formulaBitLength F) ∧
      Eval (frontendProcedure er (mainExtraStacks c)).invoke prefixSteps
        (initialData er (mainExtraStacks c) (Encoding.encodeCNF F)) before ∧
      Eval (mainProcedure c er).invoke setupSteps before ((mainProcedure c er).install before out) ∧
      (((mainProcedure c er).install before out).regs ((mainProcedure c er).registerMap (15 : Fin 16)) = true ↔
        DyadicSchedule.Ready c.k c.T n) ∧
      (SubexpPackingParameters.GoodInput n → ScalarValues c n out ∧ ThresholdValues c n out) ∧
      (∀ i : Fin 32, Retained i →
        ((mainProcedure c er).install before out).stacks
          (SubexpMainProgram.persistent (mainExtraStacks c) i) =
        before.stacks (SubexpMainProgram.persistent (mainExtraStacks c) i)) ∧
      (∀ i : Fin (stackCount c), i.val < helperSize c →
        ((mainProcedure c er).install before out).stacks (mainStack c i) = []) := by
  obtain ⟨nb, sb, ub, tp, hn, hs, hu, hp, ep⟩ :=
    prefix_execution er (mainExtraStacks c) F
  let before := prefixData er (mainExtraStacks c) (Encoding.encodeCNF F)
    (Encoding.encodeCNFBody F) nb sb ub
  have hn' : BinaryArithmetic.toNat
      (before.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 2)) = n := by
    rw [show before.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 2) = nb from
      prefix_word er (mainExtraStacks c) _ _ nb sb ub 2]
    simpa only [CounterPrograms.value_eq_toNat] using hn
  have hs' : BinaryArithmetic.toNat
      (before.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 4)) =
      SubexpPackingParameters.s n := by
    rw [show before.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 4) = sb from
      prefix_word er (mainExtraStacks c) _ _ nb sb ub 4]
    simpa only [CounterPrograms.value_eq_toNat] using hs
  have hu' : BinaryArithmetic.toNat
      (before.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 5)) =
      SubexpPackingParameters.u n := by
    rw [show before.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 5) = ub from
      prefix_word er (mainExtraStacks c) _ _ nb sb ub 5]
    simpa only [CounterPrograms.value_eq_toNat] using hu
  obtain ⟨ts, out, es, hv, ho, hf, hw⟩ := main_execution c er n before hn' hs' hu'
  exact ⟨tp, ts, before, out, hp, ep, es, hv, ho, hf, hw⟩

end SubexponentialSAT.SubexpSetupProgram

end OAI.Algorithms
