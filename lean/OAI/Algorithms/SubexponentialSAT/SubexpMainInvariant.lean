import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainBoot
import OAI.Algorithms.SubexponentialSAT.SubexpLeafContract

namespace OAI.Algorithms

/-!
# The leaf-to-leaf invariant of Main

Numerical parameters and threshold bytes are tied to the actual setup
output. Mutable persistent caches have bounded length: allowing arbitrary
lengths would invalidate the cost of clearing them on the next leaf.
The pending record stream is deliberately outside this word-size bound.
-/

namespace SubexponentialSAT.SubexpMainInvariant

open StructuredCalls SubexpMainProgram SubexpSetupProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

def ParameterPort (i : Fin 32) : Prop :=
  i.val = 2 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨
    (16 ≤ i.val ∧ i.val ≤ 27) ∨ i.val = 29

def CachePort (i : Fin 32) : Prop :=
  (12 ≤ i.val ∧ i.val ≤ 15) ∨ i.val = 28 ∨ 30 ≤ i.val

theorem parameter_excludes {i : Fin 32} (hi : ParameterPort i) :
    i ≠ 0 ∧ i ≠ 7 ∧ i ≠ 9 ∧ i ≠ 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> subst i <;> simp_all [ParameterPort]

theorem cache_excludes {i : Fin 32} (hi : CachePort i) :
    i ≠ 0 ∧ i ≠ 7 ∧ i ≠ 9 ∧ i ≠ 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> subst i <;> simp_all [CachePort]

theorem helper_within (cfg : Config) : helperSize cfg ≤ workStacks (mainExtraStacks cfg) := by
  unfold helperSize workStacks mainExtraStacks
  omega

theorem threshold_range (cfg : Config) (i : Fin (thresholdCount cfg)) :
    helperSize cfg ≤ (mainStack cfg (threshold cfg i)).val ∧
      (mainStack cfg (threshold cfg i)).val < workStacks (mainExtraStacks cfg) := by
  have hi := i.isLt
  simp only [mainStack, Fin.val_cast, threshold]
  unfold workStacks mainExtraStacks helperSize
  omega

theorem threshold_ne_persistent (cfg : Config) (i : Fin (thresholdCount cfg)) (j : Fin 32) :
    mainStack cfg (threshold cfg i) ≠ SubexpMainProgram.persistent (mainExtraStacks cfg) j := by
  intro h
  have hv := congrArg Fin.val h
  have hr := (threshold_range cfg i).2
  change (mainStack cfg (threshold cfg i)).val = workStacks (mainExtraStacks cfg) + j.val at hv
  omega

structure Stored (cfg : Config) {er : ℕ} (setup : SetupState cfg) (B : ℕ)
    (a : MainState er (mainExtraStacks cfg)) : Prop where
  parameters : ∀ i : Fin 32, ParameterPort i →
    a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) i) =
      setup.stacks (SubexpSetupProgram.persistent cfg i)
  thresholds : ∀ i : Fin (thresholdCount cfg),
    a.stacks (mainStack cfg (threshold cfg i)) = setup.stacks (threshold cfg i)
  caches : ∀ i : Fin 32, CachePort i →
    (a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) i)).length ≤ B

structure Invariant (cfg : Config) {er : ℕ} (setup : SetupState cfg) (B : ℕ)
    (a : MainState er (mainExtraStacks cfg)) : Prop extends Stored cfg setup B a where
  storage : SubexpMainReady.StorageReady (helperSize cfg) a
  leaf : a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 9) = []
  answer : a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 10) = []

variable {cfg : Config} {er : ℕ} {setup : SetupState cfg} {B : ℕ}

theorem ready {a : MainState er (mainExtraStacks cfg)} (h : Invariant cfg setup B a) :
    SubexpMainReady.StorageReady (helperSize cfg) a ∧
      a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 9) = [] ∧
      a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 10) = [] :=
  ⟨h.storage, h.leaf, h.answer⟩

theorem stored_mono {a : MainState er (mainExtraStacks cfg)} {C : ℕ}
    (h : Stored cfg setup B a) (hBC : B ≤ C) : Stored cfg setup C a :=
  ⟨h.parameters, h.thresholds, fun i hi => (h.caches i hi).trans hBC⟩

theorem stored_of_frames {a b : MainState er (mainExtraStacks cfg)}
    (ha : Stored cfg setup B a)
    (hp : ∀ i : Fin 32, ParameterPort i →
      b.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) i) =
        a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) i))
    (ht : ∀ i : Fin (thresholdCount cfg),
      b.stacks (mainStack cfg (threshold cfg i)) = a.stacks (mainStack cfg (threshold cfg i)))
    (hc : ∀ i : Fin 32, CachePort i →
      (b.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) i)).length ≤ B) :
    Stored cfg setup B b :=
  ⟨fun i hi => (hp i hi).trans (ha.parameters i hi),
    fun i => (ht i).trans (ha.thresholds i), hc⟩

theorem transferred_input_stack (base : MainState er (mainExtraStacks cfg))
    (tail bits : List Bool) (i : Fin (totalStacks (mainExtraStacks cfg)))
    (h7 : i ≠ SubexpMainProgram.persistent (mainExtraStacks cfg) 7)
    (h8 : i ≠ SubexpMainProgram.persistent (mainExtraStacks cfg) 8)
    (h9 : i ≠ SubexpMainProgram.persistent (mainExtraStacks cfg) 9) :
    (transferredData (leafInput base tail bits)).stacks i = base.stacks i := by
  simp [transferredData, StackRoutines.transferStacks, leafInput, RecordPrograms.state,
    ports, h7, h8, h9]

/-- Parsing and transferring the current record do not enlarge caches or
change the retained numerical input to a leaf. -/
theorem stored_transferred_input (base : MainState er (mainExtraStacks cfg))
    (ha : Stored cfg setup B base) (tail bits : List Bool) :
    Stored cfg setup B (transferredData (leafInput base tail bits)) := by
  have hp (i : Fin 32) (h7 : i ≠ 7) (h8 : i ≠ 8) (h9 : i ≠ 9) :=
    transferred_input_stack base tail bits (SubexpMainProgram.persistent (mainExtraStacks cfg) i)
      (fun h => h7 (SubexpMainProgram.persistent_injective _ h))
      (fun h => h8 (SubexpMainProgram.persistent_injective _ h))
      (fun h => h9 (SubexpMainProgram.persistent_injective _ h))
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hn := parameter_excludes hi
    have h8 : i ≠ 8 := by intro h; subst i; simp_all [ParameterPort]
    exact (hp i hn.2.1 h8 hn.2.2.1).trans (ha.parameters i hi)
  · intro i
    exact (transferred_input_stack base tail bits (mainStack cfg (threshold cfg i))
      (threshold_ne_persistent cfg i 7) (threshold_ne_persistent cfg i 8)
      (threshold_ne_persistent cfg i 9)).trans (ha.thresholds i)
  · intro i hi
    have hn := cache_excludes hi
    have h8 : i ≠ 8 := by intro h; subst i; simp_all [CachePort]
    rw [hp i hn.2.1 h8 hn.2.2.1]
    exact ha.caches i hi

/-- The initial cache bound comes from the same setup execution, including
the initial cutoff word on port 28. -/
theorem after_boot {n : ℕ} {hr : 32 ≤ workRegs er} {F : SAT.CNF (Fin n)}
    (run : SubexpMainBoot.Run cfg hr F)
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

/-- The actual finalizer preserves every retained parameter and cache word
once its physical decoder input has been established. -/
theorem stored_finalized (a : MainState er (mainExtraStacks cfg))
    (ha : Stored cfg setup B a) (initialRegs finalRegs : Fin 8 → Bool)
    (modulus width input word : List Bool)
    (hdecode : (SubexpMainDecode.procedure er (mainExtraStacks cfg)).project a =
      SubexpFlatCount.start initialRegs modulus width input) :
    Stored cfg setup B
      (finishedData (SubexpMainReady.result (helperSize cfg) (helper_within cfg)
        a finalRegs modulus width word)) := by
  have hf := SubexpMainReady.finished_persistent_preserved (helperSize cfg)
    (helper_within cfg) a initialRegs finalRegs modulus width input word hdecode
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hn := parameter_excludes hi
    exact (hf i hn.2.2.1 hn.2.2.2).trans (ha.parameters i hi)
  · intro i
    have hrange := threshold_range cfg i
    exact (SubexpMainReady.finished_threshold (helperSize cfg) (helper_within cfg)
      ((by norm_num : 8 ≤ 144).trans (helperSize_ge cfg))
      a finalRegs modulus width word (mainStack cfg (threshold cfg i)) hrange.1 hrange.2).trans
      (ha.thresholds i)
  · intro i hi
    have hn := cache_excludes hi
    rw [hf i hn.2.2.1 hn.2.2.2]
    exact ha.caches i hi

/-- Restores the complete loop invariant using the actual cleanup and
epilogue. The earlier producers still must prove `Stored` at their output. -/
theorem finalized (a : MainState er (mainExtraStacks cfg))
    (ha : Stored cfg setup B a) (initialRegs finalRegs : Fin 8 → Bool)
    (modulus width input word : List Bool)
    (hdecode : (SubexpMainDecode.procedure er (mainExtraStacks cfg)).project a =
      SubexpFlatCount.start initialRegs modulus width input) :
    Invariant cfg setup B
      (finishedData (SubexpMainReady.result (helperSize cfg) (helper_within cfg)
        a finalRegs modulus width word)) := by
  refine ⟨stored_finalized a ha initialRegs finalRegs modulus width input word hdecode,
    SubexpMainReady.finished_ready (helperSize cfg) (helper_within cfg)
      a finalRegs modulus width word, ?_, ?_⟩
  · exact finished_leaf _
  · exact finished_answer _

/-- The concrete producers need to establish the retained data at their
actual CRT output. Cleanup and restoration of the loop invariant then follow
from the already implemented finalizer, for every final register vector. -/
theorem stage_provider {n ell p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
    (phases : Phases er (mainExtraStacks cfg))
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (valid : SubexpLeafSemantics.Leaf n → Prop)
    (prefixLimit : List Bool → ℕ)
    (produce : ∀ G : SubexpLeafSemantics.Leaf n, valid G → [] ∉ G →
      ∀ (tail : List Bool) (base : MainState er (mainExtraStacks cfg)),
        Invariant cfg setup B base →
        ∃ c : SubexpLayoutSpec.Parameters p k Δ r tau,
        ∃ layout : SubexpLayoutSpec.Layout (E := SubexpActualRing.E p)
          (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)).toPattern c,
        ∃ stages : SubexpLeafContract.ReconstructionStages phases G hell hcap layout
          (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)),
          stages.prefixSteps ≤ prefixLimit (ExecQuantitativeSparsify.encodeRawFormula G) ∧
          Stored cfg setup B stages.afterCRT) :
    SubexpLeafContract.StageProvider (k := k) (Δ := Δ) (r := r) (tau := tau)
      phases (helperSize cfg) (helper_within cfg) hell hcap valid
      (Invariant cfg setup B) prefixLimit := by
  intro G hG hne tail base hb
  obtain ⟨c, layout, stages, hcost, hstored⟩ := produce G hG hne tail base hb
  refine ⟨c, layout, stages, hcost, ?_⟩
  intro rf
  exact finalized stages.afterCRT hstored stages.decodeRegs rf stages.modulus.bits
    stages.width (SubexpFlatCount.flatPolynomial [stages.output]) stages.output.c0.val stages.decodeReady

end SubexponentialSAT.SubexpMainInvariant

end OAI.Algorithms
