import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutWordBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutSizes
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawBoot

namespace OAI.Algorithms

/-! Selected layout input words from the actual ordered-raw boot.

The original order of clauses and literals is retained by the boot record.
The bounded parameter words come from that record's own setup execution;
no canonical-input boot is substituted.
-/

namespace SubexponentialSAT.SubexpOrderedRawLayoutInitialBounds

open StructuredCalls SubexpMainProgram SubexpSetupProgram
open SubexpMainInvariant SubexpMainLayoutWordBounds

variable {cfg : Config} {er n B : ℕ} {hr : 32 ≤ workRegs er}
variable {F : SubexpOrderedRawPrefix.Formula n}

theorem setup_parameter_length (run : SubexpOrderedRawBoot.Run cfg hr F)
    (hwords : SubexpSetupStorage.WordBound B run.afterSetup)
    (i : Fin 32) (hi : ParameterPort i) :
    (run.setupOutput.stacks (SubexpSetupProgram.persistent cfg i)).length ≤ B := by
  have hn := parameter_excludes hi
  rw [← run.setup_word i hn.1 hn.2.1]
  exact run.parameter_word_bound hwords i hn.1 hn.2.1

/-- The physical parser/transfer preserves the selected parameters and
caches, clears its payload word, and installs the exact current leaf.
The pending stream has no length premise. -/
theorem transferred_raw_bound (run : SubexpOrderedRawBoot.Run cfg hr F)
    (hwords : SubexpSetupStorage.WordBound B run.afterSetup)
    (hhelper : 672 ≤ helperSize cfg)
    (base : MainState er (mainExtraStacks cfg))
    (hinvariant : Invariant cfg run.setupOutput B base)
    (tail bits : List Bool) :
    RelevantWordBound (B+bits.length) (transferredData (leafInput base tail bits)) := by
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

/-- The valid leaf supplies its actual serialized-size bound. This is
compatible with `MainLayoutOutputBounds.seed_output_bound` on the same
native layout run, since that theorem is independent of the boot route. -/
theorem transferred_leaf_bound (run : SubexpOrderedRawBoot.Run cfg hr F)
    (hwords : SubexpSetupStorage.WordBound B run.afterSetup)
    (hhelper : 672 ≤ helperSize cfg)
    (base : MainState er (mainExtraStacks cfg))
    (hinvariant : Invariant cfg run.setupOutput B base)
    (tail : List Bool) (G : SubexpLeafData.Leaf n)
    (valid : SubexpMainAssembly.validLeaf cfg n G)
    {L : ℕ} (hnL : n ≤ L) :
    RelevantWordBound (B+(8*cfg.k+5)*(L+1)^(2*cfg.k+1))
      (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) := by
  exact SubexpMainLayoutWordBounds.mono
    (transferred_raw_bound run hwords hhelper base hinvariant tail
      (ExecQuantitativeSparsify.encodeRawFormula G))
    (Nat.add_le_add_left (SubexpMainLayoutSizes.raw_leaf_bytes G valid hnL) B)

end SubexponentialSAT.SubexpOrderedRawLayoutInitialBounds

end OAI.Algorithms
