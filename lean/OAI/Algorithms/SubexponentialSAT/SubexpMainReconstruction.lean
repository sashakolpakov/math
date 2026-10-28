import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainInvariant
import OAI.Algorithms.SubexponentialSAT.SubexpMainCRTSelected

namespace OAI.Algorithms

/-!
# Completing real leaf stages with the selected CRT program

The remaining layout/moment producer supplies actual traces and the physical
node/jet readback for the same typed layout. This module invokes the concrete
CRT program, obtains its singleton value and decoder state, and preserves the
retained-data invariant. It does not assume a CRT execution or output value.
-/

namespace SubexponentialSAT.SubexpMainReconstruction

open StructuredCalls SubexpMainProgram SubexpSetupProgram SubexpLayoutSpec
open SubexpLiftRing SubexpQuarticRing SubexpLeafSemantics

variable {cfg : Config} {er n ell p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]

local notation "D" => SubexpLeafContract.dimension n ell
local notation "B" => SubexpLeafContract.wordWidth n ell p
local notation "coeffs" => QuarticSearch.liftedCoefficients p (D + 1)

/-- Every semantic field refers to the actual word or array in the given
state. The concrete moment producer must establish these fields. -/
structure Readback (G : Leaf n) (hell : 0 < ell) (hcap : 2 ^ ell ≤ p)
    {c : Parameters p k Δ r tau}
    (layout : Layout (E := SubexpActualRing.E p)
      (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)).toPattern c)
    (alloc : SubexpMainCRT.Allocation (mainExtraStacks cfg))
    (a : MainState er (mainExtraStacks cfg)) where
  modulus : SubexpPreparedQuartic.Modulus p (D + 1)
  reduction : SubexpCRTSelectedInput.Coefficient p D
  one : SubexpCRTSelectedInput.Coefficient p D
  minusOne : Word B
  width : List Bool
  exponent : List Bool
  nodes : Fin c.Q → SubexpCRTSelectedInput.Coefficient p D
  jets : Fin c.Q → SubexpCRTSelectedInput.Jet p D
  width_length : width.length = B
  reduction_value : reduction.map (wordValue p (D + 1)) = reductionData coeffs
  one_value : SubexpCRTSelectedInput.decode p D one = 1
  minusOne_value : wordValue p (D + 1) minusOne = -1
  exponent_value : BinaryArithmetic.toNat exponent = p ^ 4 - 2
  node_values : ∀ i, SubexpCRTSelectedInput.decode p D (nodes i) =
    SubexpCRTAtZero.selectedNode
      (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)) layout i
  jet_values : ∀ i, SubexpCRTSelectedInput.denote p D (jets i) =
    SubexpCRTSelectedInput.selectedJet
      (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)) layout i
  modulus_word : a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 12) = modulus.bits
  width_word : a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 13) = width
  reduction_word : a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 14) =
    SubexpFlatAdd.encode reduction
  exponent_word : a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 29) = exponent
  one_word : a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 30) = SubexpFlatAdd.encode one
  minusOne_word : a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 31) = minusOne.val
  dimension_word : CounterPrograms.value
    (a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 19)) = D
  node_words : a.stacks (SubexpMainCRT.ordinary alloc 256) =
    (List.finRange c.Q).flatMap (fun i => SubexpFlatAdd.encode (nodes i))
  jet_words : a.stacks (SubexpMainCRT.ordinary alloc 265) =
    (List.finRange c.Q).flatMap
      (fun i => SubexpPolynomialPowerProgram.encode p (D + 1) (jets i))

def Readback.bound {G : Leaf n} {hell : 0 < ell} {hcap : 2 ^ ell ≤ p}
    {c : Parameters p k Δ r tau}
    {layout : Layout (E := SubexpActualRing.E p)
      (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)).toPattern c}
    {alloc : SubexpMainCRT.Allocation (mainExtraStacks cfg)}
    {a : MainState er (mainExtraStacks cfg)} (input : Readback G hell hcap layout alloc a) : ℕ :=
  SubexpMainCRTSelected.runtimeBound (p := p) (V := Fin (ChunkPartition.count n ell))
    alloc a c.Q input.exponent

/-- The two upstream traces remain explicit. The third trace, its value,
decoder readiness, and preserved storage come from the real CRT execution. -/
theorem complete (G : Leaf n) (hell : 0 < ell) (hcap : 2 ^ ell ≤ p)
    {c : Parameters p k Δ r tau}
    (layout : Layout (E := SubexpActualRing.E p)
      (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)).toPattern c)
    (alloc : SubexpMainCRT.Allocation (mainExtraStacks cfg))
    (halloc : alloc.ordinaryCount = helperSize cfg)
    (phases : Phases er (mainExtraStacks cfg))
    (hcrt : phases.crt = SubexpMainCRT.procedure er alloc)
    (start afterLayout afterMoments : MainState er (mainExtraStacks cfg))
    (layoutSteps momentSteps : ℕ)
    (layoutTrace : Eval phases.layout.invoke layoutSteps (transferredData start) afterLayout)
    (momentTrace : Eval phases.moments.invoke momentSteps afterLayout afterMoments)
    (input : Readback G hell hcap layout alloc afterMoments)
    {setup : SetupState cfg} {cacheSize : ℕ}
    (stored : SubexpMainInvariant.Stored cfg setup cacheSize afterMoments)
    (sourceFrame : afterMoments.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 7) =
      (transferredData start).stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 7))
    (payloadFrame : afterMoments.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 8) =
      (transferredData start).stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 8))
    (leafFrame : afterMoments.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 9) =
      (transferredData start).stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 9))
    (hn : 0 < n) :
    ∃ stages : SubexpLeafContract.ReconstructionStages phases G hell hcap layout start,
      stages.prefixSteps ≤ layoutSteps + momentSteps + input.bound ∧
      SubexpMainInvariant.Stored cfg setup cacheSize stages.afterCRT := by
  have hD : 0 < D := by
    simpa only [Fintype.card_fin] using (ChunkPartition.count_pos_iff hell).mpr hn
  obtain ⟨crtSteps, htime, afterCRT, output, trace, value, _, decodeReady,
      persistentFrame, thresholdFrame, _⟩ :=
    SubexpMainCRTSelected.execution
      (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G))
      layout alloc afterMoments input.modulus input.reduction
      input.one input.minusOne input.width input.exponent input.nodes input.jets hD
      input.width_length input.reduction_value input.one_value input.minusOne_value
      input.exponent_value input.node_values input.jet_values input.modulus_word input.width_word
      input.reduction_word input.exponent_word input.one_word input.minusOne_word
      input.dimension_word input.node_words input.jet_words
  let stages : SubexpLeafContract.ReconstructionStages phases G hell hcap layout start := {
    afterLayout := afterLayout, afterMoments := afterMoments, afterCRT := afterCRT
    layoutSteps := layoutSteps, momentSteps := momentSteps, crtSteps := crtSteps
    layoutTrace := layoutTrace, momentTrace := momentTrace
    crtTrace := by simpa only [hcrt] using trace
    modulus := input.modulus, output := output
    decodeRegs := ((SubexpMainDecode.procedure er (mainExtraStacks cfg)).project afterCRT).regs
    width := input.width, width_length := input.width_length
    decodeReady := decodeReady, reconstructed := value
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

end SubexponentialSAT.SubexpMainReconstruction

end OAI.Algorithms
