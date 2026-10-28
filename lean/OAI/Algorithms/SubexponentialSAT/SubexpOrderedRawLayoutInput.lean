import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawParameterValues
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutInput

namespace OAI.Algorithms

/-! The shared native layout input, derived from the ordered boot and the
same real parser transfer. Its leaf bytes and ordinary workspace are exact. -/

namespace SubexponentialSAT.SubexpOrderedRawLayoutInput

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupProgram
open SubexpPackingParameters
open SubexpMainInvariant (Stored Invariant)
open SubexpLayoutPorts (Allocation ordinary)
open SubexpMainLayoutInput (Ready castLeaf_sparse castLeaf_no_empty castLeaf_bytes raw_bytes)

variable {cfg : Config} {er n B : ℕ} {hr : 32 ≤ workRegs er}
variable {F : SubexpOrderedRawPrefix.Formula n} {a : MainState er (mainExtraStacks cfg)}

theorem ready_from_boot (alloc : Allocation (mainExtraStacks cfg))
    (run : SubexpOrderedRawBoot.Run cfg hr F) (stored : Stored cfg run.setupOutput B a)
    (good : GoodInput n) (G : SubexpLeafData.Leaf n)
    (valid : SubexpMainAssembly.validLeaf cfg n G) (no_empty : [] ∉ G)
    (leaf : a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 9) =
      ExecQuantitativeSparsify.encodeRawFormula G)
    (empty : ∀ i : Fin 672, a.stacks (ordinary alloc i) = []) :
    Ready alloc a n cfg.k cfg.T G := by
  have hn := SubexpOrderedRawParameterValues.sourceInputs_variableCount alloc run stored
  obtain ⟨hell, hwidth, hp, hD, hcap, hdelta⟩ :=
    SubexpOrderedRawParameterValues.sourceInputs_ready alloc run stored good
  have hs := SubexpOrderedRawParameterValues.scalarValues run stored
  refine ⟨hn, hell, hwidth, hp, hD, hcap,
    castLeaf_sparse hn.symm G valid.1, castLeaf_no_empty hn.symm G no_empty,
    ?_, hdelta, SubexpOrderedRawParameterValues.sourceInputs_metadata alloc run stored,
    empty, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [SubexpMainParameterValues.sourceInputs_leaf, leaf, ← castLeaf_bytes hn.symm G]
    exact raw_bytes _
  · simpa only [CounterPrograms.value_eq_toNat, main_project_word] using hs.prime
  · simpa only [CounterPrograms.value_eq_toNat, main_project_word] using hs.colors
  · simpa only [CounterPrograms.value_eq_toNat, main_project_word, DyadicSchedule.Q,
      SubexpParameters.sizeQ] using hs.Q
  · simpa only [CounterPrograms.value_eq_toNat, main_project_word] using hs.R
  · rw [SubexpOrderedRawParameterValues.sourceInputs_dimension alloc run stored]
    simpa only [main_project_word] using hs.precision
  · simpa only [main_project_word] using hs.inverseExponent

/-- The parser transfer establishes the actual source bytes and all 672
ordinary empty inputs, while preserving the same setup state and cache cap. -/
theorem ready_transferred (alloc : Allocation (mainExtraStacks cfg))
    (halloc : alloc.ordinaryCount = helperSize cfg)
    (run : SubexpOrderedRawBoot.Run cfg hr F) (base : MainState er (mainExtraStacks cfg))
    (invariant : Invariant cfg run.setupOutput B base) (good : GoodInput n)
    (G : SubexpLeafData.Leaf n) (valid : SubexpMainAssembly.validLeaf cfg n G)
    (no_empty : [] ∉ G) (tail : List Bool) :
    Ready alloc (transferredData (leafInput base tail
      (ExecQuantitativeSparsify.encodeRawFormula G))) n cfg.k cfg.T G := by
  apply ready_from_boot alloc run
    (SubexpMainInvariant.stored_transferred_input base invariant.toStored tail _)
    good G valid no_empty
  · exact (transfer_leafInput base tail _ invariant.leaf).1
  · have hs := SubexpMainReady.transferred_ready (helperSize cfg)
      (SubexpMainInvariant.helper_within cfg)
      (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))
      (SubexpMainReady.leafInput_ready (helperSize cfg)
        (SubexpMainInvariant.helper_within cfg) base tail
        (ExecQuantitativeSparsify.encodeRawFormula G) invariant.storage)
    intro i
    apply hs.2
    change i.val < helperSize cfg
    have hi := i.isLt
    have ha := alloc.enough
    omega

end SubexponentialSAT.SubexpOrderedRawLayoutInput

end OAI.Algorithms
