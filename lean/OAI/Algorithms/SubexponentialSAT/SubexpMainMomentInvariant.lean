import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentReady
import OAI.Algorithms.SubexponentialSAT.SubexpMainInvariant

namespace OAI.Algorithms

/-!
# Retained data through the actual moment-phase handoff

The collector's only persistent ports are the target modulus and scalar
width. Their explicit preservation, together with its physical port map,
preserves every persistent word and every threshold. The setup and scratch
clear have the same frame property.
-/

namespace SubexponentialSAT.SubexpMainMomentInvariant

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupProgram
open SubexpLayoutPorts (Allocation ordinary)

theorem avoids_persistent {es : ℕ} (alloc : Allocation es) (i : Fin 32)
    (h12 : i ≠ 12) (h13 : i ≠ 13) :
    ¬ ∃ j, SubexpMainMomentPorts.stackMap alloc j = SubexpMainProgram.persistent es i := by
  rintro ⟨j, hj⟩
  by_cases h5 : j = 5
  · simp only [SubexpMainMomentPorts.stackMap, ite_eq_left h5] at hj
    exact h12 ((persistent_injective es hj).symm)
  · by_cases h10 : j = 10
    · simp only [SubexpMainMomentPorts.stackMap, ite_eq_right h5, ite_eq_left h10] at hj
      exact h13 ((persistent_injective es hj).symm)
    · exact SubexpMainMomentPorts.baseMap_ne_persistent alloc j i
        (by simpa only [SubexpMainMomentPorts.stackMap, ite_eq_right h5, ite_eq_right h10] using hj)

theorem avoids_threshold {es : ℕ} (alloc : Allocation es)
    (i : Fin (totalStacks es)) (hlo : alloc.ordinaryCount ≤ i.val)
    (hhi : i.val < workStacks es) :
    ¬ ∃ j, SubexpMainMomentPorts.stackMap alloc j = i := by
  rintro ⟨j, hj⟩
  have h672 := alloc.enough.trans hlo
  by_cases h5 : j = 5
  · subst j
    rw [SubexpMainMomentPorts.stackMap_modulus] at hj
    have hv := congrArg Fin.val hj
    simp only [SubexpMainProgram.persistent, Fin.val_natAdd] at hv
    omega
  · by_cases h10 : j = 10
    · subst j
      rw [SubexpMainMomentPorts.stackMap_width] at hj
      have hv := congrArg Fin.val hj
      simp only [SubexpMainProgram.persistent, Fin.val_natAdd] at hv
      omega
    · have hb := SubexpMainMomentPorts.baseMap_below alloc j
      have hs : SubexpMainMomentPorts.stackMap alloc j =
          SubexpMainMomentPorts.baseMap alloc j := by
        simp only [SubexpMainMomentPorts.stackMap, ite_eq_right h5, ite_eq_right h10]
      have hv := congrArg Fin.val (hs.symm.trans hj)
      omega

theorem initializer_persistent {er es D : ℕ} {alloc : Allocation es}
    {a b : MainState er es} (h : SubexpMainNodeInitialization.Result alloc a b D)
    (i : Fin 32) :
    b.stacks (SubexpMainProgram.persistent es i) = a.stacks (SubexpMainProgram.persistent es i) := by
  by_cases h12 : i = 12
  · subst i
    simpa only [SubexpMainMomentPorts.stackMap_modulus] using
      SubexpMainMomentReady.initializer_frame h 5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
  · by_cases h13 : i = 13
    · subst i
      simpa only [SubexpMainMomentPorts.stackMap_width] using
        SubexpMainMomentReady.initializer_frame h 10 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact h.frame _ (avoids_persistent alloc i h12 h13)

theorem prepared_threshold {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin (totalStacks es)) (hlo : alloc.ordinaryCount ≤ i.val) :
    (SubexpMainNodeSetup.prepared alloc a).stacks i = a.stacks i := by
  have h672 := alloc.enough.trans hlo
  rw [SubexpMainNodeSetup.prepared, SubexpMainNodeReduction.installed_threshold alloc _ i hlo,
    SubexpMainNodeSetup.headed, SubexpMainNodeHeader.installed_frame alloc _ i]
  · exact SubexpMainNodePreclear.result_high_frame alloc a i (by omega)
  · intro j hj
    have hv := congrArg Fin.val hj
    fin_cases j <;> norm_num [SubexpMainNodeHeader.targetPort, ordinary] at hv <;> omega
  · intro hj
    have hv := congrArg Fin.val hj
    change 319 = i.val at hv
    omega

theorem scratch_persistent {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 32) :
    (SubexpMainNodeScratch.result alloc a).stacks (SubexpMainProgram.persistent es i) =
      a.stacks (SubexpMainProgram.persistent es i) := by
  apply SubexpMainNodeScratch.result_frame
  intro h
  have hv := congrArg Fin.val h
  have hb := alloc.enough.trans alloc.within
  change workStacks es + i.val = 243 at hv
  omega

theorem collector_persistent {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : SubexpNodeWideLoop.Data)
    (h5 : out.stacks 5 = (SubexpMainMoments.projected alloc a).stacks 5)
    (h10 : out.stacks 10 = (SubexpMainMoments.projected alloc a).stacks 10)
    (i : Fin 32) :
    (SubexpMainMoments.installed alloc a out).stacks (SubexpMainProgram.persistent es i) =
      a.stacks (SubexpMainProgram.persistent es i) := by
  by_cases h12 : i = 12
  · subst i
    exact (SubexpMainMoments.installed_stack alloc a out 5).trans h5
  · by_cases h13 : i = 13
    · subst i
      exact (SubexpMainMoments.installed_stack alloc a out 10).trans h10
    · exact embedState_stack_frame _ _ _ _ _ (avoids_persistent alloc i h12 h13)

theorem persistent_frame {er es D : ℕ} {alloc : Allocation es} {a b : MainState er es}
    (h : SubexpMainNodeInitialization.Result alloc (SubexpMainNodeSetup.prepared alloc a) b D)
    (out : SubexpNodeWideLoop.Data)
    (h5 : out.stacks 5 = (SubexpMainMoments.projected alloc (SubexpMainNodeScratch.result alloc b)).stacks 5)
    (h10 : out.stacks 10 = (SubexpMainMoments.projected alloc (SubexpMainNodeScratch.result alloc b)).stacks 10)
    (i : Fin 32) :
    (SubexpMainMoments.installed alloc (SubexpMainNodeScratch.result alloc b) out).stacks
        (SubexpMainProgram.persistent es i) = a.stacks (SubexpMainProgram.persistent es i) :=
  (collector_persistent alloc _ out h5 h10 i).trans
    ((scratch_persistent alloc b i).trans
      ((initializer_persistent h i).trans (SubexpMainNodeSetup.prepared_persistent alloc a i)))

theorem threshold_frame {er es D : ℕ} {alloc : Allocation es} {a b : MainState er es}
    (h : SubexpMainNodeInitialization.Result alloc (SubexpMainNodeSetup.prepared alloc a) b D)
    (out : SubexpNodeWideLoop.Data) (i : Fin (totalStacks es))
    (hlo : alloc.ordinaryCount ≤ i.val) (hhi : i.val < workStacks es) :
    (SubexpMainMoments.installed alloc (SubexpMainNodeScratch.result alloc b) out).stacks i =
      a.stacks i := by
  have h672 := alloc.enough.trans hlo
  have hc : (SubexpMainMoments.installed alloc (SubexpMainNodeScratch.result alloc b) out).stacks i =
      (SubexpMainNodeScratch.result alloc b).stacks i :=
    embedState_stack_frame _ _ _ _ _ (avoids_threshold alloc i hlo hhi)
  have hs := SubexpMainNodeScratch.result_frame alloc b i (by
    intro he
    have hv := congrArg Fin.val he
    change i.val = 243 at hv
    omega)
  exact hc.trans (hs.trans ((h.frame i (avoids_threshold alloc i hlo hhi)).trans
    (prepared_threshold alloc a i hlo)))

theorem stored {cfg : Config} {er D : ℕ} {alloc : Allocation (mainExtraStacks cfg)}
    {a b : MainState er (mainExtraStacks cfg)}
    (h : SubexpMainNodeInitialization.Result alloc (SubexpMainNodeSetup.prepared alloc a) b D)
    (halloc : alloc.ordinaryCount = helperSize cfg)
    (out : SubexpNodeWideLoop.Data)
    (h5 : out.stacks 5 = (SubexpMainMoments.projected alloc (SubexpMainNodeScratch.result alloc b)).stacks 5)
    (h10 : out.stacks 10 = (SubexpMainMoments.projected alloc (SubexpMainNodeScratch.result alloc b)).stacks 10)
    {setup : SetupState cfg} {B : ℕ} (initial : SubexpMainInvariant.Stored cfg setup B a) :
    SubexpMainInvariant.Stored cfg setup B
      (SubexpMainMoments.installed alloc (SubexpMainNodeScratch.result alloc b) out) := by
  apply SubexpMainInvariant.stored_of_frames initial
  · intro i _
    exact persistent_frame h out h5 h10 i
  · intro i
    have hr := SubexpMainInvariant.threshold_range cfg i
    apply threshold_frame h out _ _ hr.2
    rw [halloc]
    exact hr.1
  · intro i hi
    rw [persistent_frame h out h5 h10 i]
    exact initial.caches i hi

end SubexponentialSAT.SubexpMainMomentInvariant

end OAI.Algorithms
