import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutWordBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutSizes

namespace OAI.Algorithms

/-! Selected word bounds at the actual entry to a leaf's layout phase.

Only retained parameters, bounded caches, the current leaf, and ordinary
layout storage are selected. The pending record stream has no size premise.
-/

namespace SubexponentialSAT.SubexpMainLayoutInitialBounds

open StructuredCalls SubexpMainProgram SubexpSetupProgram
open SubexpMainInvariant SubexpMainLayoutWordBounds

variable {cfg : Config} {er n B : ℕ} {hr : 32 ≤ workRegs er}
variable {F : SAT.CNF (Fin n)}

/-- The parameter bytes in the invariant retain the bound of the same
completed setup execution. No bound on the later pending queue is used. -/
theorem setup_parameter_length (run : SubexpMainBoot.Run cfg hr F)
    (hwords : SubexpSetupStorage.WordBound B run.afterSetup)
    (i : Fin 32) (hi : ParameterPort i) :
    (run.setupOutput.stacks (SubexpSetupProgram.persistent cfg i)).length ≤ B := by
  have hn := parameter_excludes hi
  rw [← run.setup_word i hn.1 hn.2.1]
  exact run.parameter_word_bound hwords i hn.1 hn.2.1

/-- Parsing and physically transferring a leaf preserves the bounded
parameter/cache words and initializes the current-leaf word to exactly
`bits`. All selected ordinary storage is empty at this point. -/
theorem transferred_raw_bound (run : SubexpMainBoot.Run cfg hr F)
    (hwords : SubexpSetupStorage.WordBound B run.afterSetup)
    (hhelper : 672 ≤ helperSize cfg)
    (base : MainState er (mainExtraStacks cfg))
    (hinvariant : Invariant cfg run.setupOutput B base)
    (tail bits : List Bool) :
    RelevantWordBound (B + bits.length) (transferredData (leafInput base tail bits)) := by
  have hstored := stored_transferred_input base hinvariant.toStored tail bits
  have hstorage := SubexpMainReady.transferred_ready (helperSize cfg) (helper_within cfg)
    (leafInput base tail bits)
    (SubexpMainReady.leafInput_ready (helperSize cfg) (helper_within cfg)
      base tail bits hinvariant.storage)
  intro i hi
  rcases hi with ho | ⟨j, rfl, hj⟩
  · have hz := hstorage.2 i (ho.trans_le hhelper)
    simp only [hz, List.length_nil]
    exact Nat.zero_le _
  · rcases hj with hp | hc | rfl
    · rw [hstored.parameters j hp]
      exact (setup_parameter_length run hwords j hp).trans (Nat.le_add_right B bits.length)
    · exact (hstored.caches j hc).trans (Nat.le_add_right B bits.length)
    · rw [(transfer_leafInput base tail bits hinvariant.leaf).1]
      exact Nat.le_add_left bits.length B

/-- The current leaf's actual encoded size supplies a fixed polynomial
entry bound. The pending tail remains unrestricted. -/
theorem transferred_leaf_bound (run : SubexpMainBoot.Run cfg hr F)
    (hwords : SubexpSetupStorage.WordBound B run.afterSetup)
    (hhelper : 672 ≤ helperSize cfg)
    (base : MainState er (mainExtraStacks cfg))
    (hinvariant : Invariant cfg run.setupOutput B base)
    (tail : List Bool) (G : SubexpLeafData.Leaf n)
    (valid : SubexpMainAssembly.validLeaf cfg n G)
    {L : ℕ} (hnL : n ≤ L) :
    RelevantWordBound (B + (8 * cfg.k + 5) * (L + 1) ^ (2 * cfg.k + 1))
      (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) := by
  exact SubexpMainLayoutWordBounds.mono
    (transferred_raw_bound run hwords hhelper base hinvariant tail
      (ExecQuantitativeSparsify.encodeRawFormula G))
    (Nat.add_le_add_left (SubexpMainLayoutSizes.raw_leaf_bytes G valid hnL) B)

end SubexponentialSAT.SubexpMainLayoutInitialBounds

end OAI.Algorithms
