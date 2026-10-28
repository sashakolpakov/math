import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawBoot
import OAI.Algorithms.SubexponentialSAT.SubexpMainInvariant

namespace OAI.Algorithms

/-! The unchanged Main leaf invariant after the actual ordered-input boot.
The cache bound comes from the same retained numerical setup execution. -/

namespace SubexponentialSAT.SubexpOrderedRawInvariant

open StructuredCalls SubexpMainProgram SubexpSetupProgram SubexpMainInvariant

theorem after_boot {cfg : Config} {er n B : ℕ} {hr : 32 ≤ workRegs er}
    {F : SubexpOrderedRawPrefix.Formula n}
    (run : SubexpOrderedRawBoot.Run cfg hr F)
    (hw : SubexpSetupStorage.WordBound B run.afterSetup) :
    Invariant cfg run.setupOutput B run.afterSparsify := by
  refine ⟨⟨?_, ?_, ?_⟩, run.storageReady, ?_, ?_⟩
  · intro i hi
    have hn := parameter_excludes hi
    exact run.setup_word i hn.1 hn.2.1
  · intro i
    exact (run.outcome.threshold_frame i).trans
      (embedState_stack _ _ _ _ (mainProcedure cfg er).stack.injective (threshold cfg i))
  · intro i hi
    have hn := cache_excludes hi
    exact run.parameter_word_bound hw i hn.1 hn.2.1
  · exact run.persistent_empty 9 (by decide) (by decide)
  · exact run.persistent_empty 10 (by decide) (by decide)

end SubexponentialSAT.SubexpOrderedRawInvariant

end OAI.Algorithms
