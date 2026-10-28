import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainReconstruction
import OAI.Algorithms.SubexponentialSAT.SubexpMainSystemReadback
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedLayoutTransport

namespace OAI.Algorithms

/-!
# Reconstructing from the physically ordered factor system

The actual CRT program consumes the numeric system's node and jet arrays.
Only its final reconstructed value is transported back to the original SAT
factor indexing. The layout is pulled back along that same factor order.
-/

namespace SubexponentialSAT.SubexpMainOrderedReconstruction

open StructuredCalls SubexpMainProgram SubexpSetupProgram SubexpLayoutSpec
open SubexpLiftRing SubexpQuarticRing SubexpLeafSemantics
open Subexp.OrderedScopeSystem Subexp.ConstructivePacking

variable {cfg : Config} {er n ell p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]

abbrev FactorIndex (G : Leaf n) (ell : ℕ) :=
  Fin (ChunkPartition.count n ell) ⊕ {C // C ∈ ExecCNF.formulaSet G}

variable (G : Leaf n) (hell : 0 < ell) (hcap : 2 ^ ell ≤ p)

local notation "S" => SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)
local notation "D" => ChunkPartition.count n ell

theorem complete
    (factors : FiniteEnumeration (FactorIndex G ell))
    (scopeLists : FactorIndex G ell → List (Fin D))
    (scopeMem : ∀ e v, v ∈ scopeLists e ↔ v ∈ (S).scope e)
    (hP : (S).toPattern.Bounded k Δ)
    {c : Parameters p k Δ r tau}
    (layout : Layout (E := SubexpActualRing.E p)
      (system S factors scopeLists scopeMem).toPattern c)
    (alloc : SubexpMainCRT.Allocation (mainExtraStacks cfg))
    (halloc : alloc.ordinaryCount = helperSize cfg)
    (phases : Phases er (mainExtraStacks cfg))
    (hcrt : phases.crt = SubexpMainCRT.procedure er alloc)
    (start afterLayout afterMoments : MainState er (mainExtraStacks cfg))
    (layoutSteps momentSteps : ℕ)
    (layoutTrace : Eval phases.layout.invoke layoutSteps (transferredData start) afterLayout)
    (momentTrace : Eval phases.moments.invoke momentSteps afterLayout afterMoments)
    (input : SubexpMainSystemReadback.Readback (system S factors scopeLists scopeMem)
      layout alloc afterMoments)
    {setup : SetupState cfg} {cacheSize : ℕ}
    (stored : SubexpMainInvariant.Stored cfg setup cacheSize afterMoments)
    (sourceFrame : afterMoments.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 7) =
      (transferredData start).stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 7))
    (payloadFrame : afterMoments.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 8) =
      (transferredData start).stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 8))
    (leafFrame : afterMoments.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 9) =
      (transferredData start).stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 9))
    (hn : 0 < n) :
    ∃ stages : SubexpLeafContract.ReconstructionStages phases G hell hcap
        (SubexpOrderedLayoutTransport.pullback S factors scopeLists scopeMem hP layout) start,
      stages.prefixSteps ≤ layoutSteps + momentSteps + input.bound ∧
      SubexpMainInvariant.Stored cfg setup cacheSize stages.afterCRT := by
  have hD : 0 < D := (ChunkPartition.count_pos_iff hell).mpr hn
  have hcard : 0 < Fintype.card (Fin D) := by simpa using hD
  obtain ⟨crtSteps, htime, afterCRT, output, trace, value, _, decodeReady,
      persistentFrame, thresholdFrame, _⟩ :=
    SubexpMainCRTSelected.execution (system S factors scopeLists scopeMem)
      layout alloc afterMoments input.modulus input.reduction
      input.one input.minusOne input.width input.exponent input.nodes input.jets hcard
      input.width_length input.reduction_value input.one_value input.minusOne_value
      input.exponent_value input.node_values input.jet_values input.modulus_word input.width_word
      input.reduction_word input.exponent_word input.one_word input.minusOne_word
      input.dimension_word input.node_words input.jet_words
  let stages : SubexpLeafContract.ReconstructionStages phases G hell hcap
      (SubexpOrderedLayoutTransport.pullback S factors scopeLists scopeMem hP layout) start := {
    afterLayout := afterLayout, afterMoments := afterMoments, afterCRT := afterCRT
    layoutSteps := layoutSteps, momentSteps := momentSteps, crtSteps := crtSteps
    layoutTrace := layoutTrace, momentTrace := momentTrace
    crtTrace := by simpa only [hcrt] using trace
    modulus := input.modulus, output := output
    decodeRegs := ((SubexpMainDecode.procedure er (mainExtraStacks cfg)).project afterCRT).regs
    width := input.width, width_length := input.width_length
    decodeReady := decodeReady
    reconstructed := value.trans
      (SubexpOrderedLayoutTransport.selectedValue_pullback S factors scopeLists scopeMem hP layout hD)
    source_frame := (persistentFrame 7 (by decide)).trans sourceFrame
    payload_frame := (persistentFrame 8 (by decide)).trans payloadFrame
    leaf_frame := (persistentFrame 9 (by decide)).trans leafFrame }
  refine ⟨stages, ?_, ?_⟩
  · change layoutSteps + (momentSteps + crtSteps) ≤ _
    change crtSteps ≤ input.bound at htime
    omega
  · change SubexpMainInvariant.Stored cfg setup cacheSize afterCRT
    apply SubexpMainInvariant.stored_of_frames stored
    · intro i hi
      exact persistentFrame i (SubexpMainInvariant.parameter_excludes hi).2.2.2
    · intro i
      have hrange := SubexpMainInvariant.threshold_range cfg i
      apply thresholdFrame _ _ hrange.2
      rw [halloc]
      exact hrange.1
    · intro i hi
      rw [persistentFrame i (SubexpMainInvariant.cache_excludes hi).2.2.2]
      exact stored.caches i hi

end SubexponentialSAT.SubexpMainOrderedReconstruction

end OAI.Algorithms
