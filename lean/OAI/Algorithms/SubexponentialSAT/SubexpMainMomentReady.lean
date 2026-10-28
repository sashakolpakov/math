import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainMoments
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWorkspace

namespace OAI.Algorithms

/-! The actual setup and final scratch clear establish the reusable node
workspace. Every non-master word is empty before the first node visit. -/

namespace SubexponentialSAT.SubexpMainMomentReady

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary master)

attribute [local simp] Fin.coe_ofNat_eq_mod

def workerStacks {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    SubexpNodeWorkspace.Store :=
  fun i => a.stacks (SubexpMainMomentPorts.stackMap alloc (i.castAdd 64))

theorem initializer_frame {er es : ℕ} {alloc : Allocation es}
    {a b : MainState er es} {D : ℕ}
    (h : SubexpMainNodeInitialization.Result alloc a b D) (i : Fin 352)
    (h25 : i ≠ 25) (h92 : i ≠ 92) (h109 : i ≠ 109)
    (h122 : i ≠ 122) (h123 : i ≠ 123) (h124 : i ≠ 124)
    (h125 : i ≠ 125) (h127 : i ≠ 127) :
    b.stacks (SubexpMainMomentPorts.stackMap alloc i) =
      a.stacks (SubexpMainMomentPorts.stackMap alloc i) := by
  have hw := h.words i
  simp only [SubexpNodeWideInitialization.resultStacks,
    SubexpNodeWideSetup.resultStacks, SubexpNodeWideSetup.localResult,
    SubexpNodeWideInitialization.dimensionResult,
    Function.update_of_ne h25, Function.update_of_ne h92,
    Function.update_of_ne h122, Function.update_of_ne h123,
    Function.update_of_ne h124, Function.update_of_ne h125,
    Function.update_of_ne h127] at hw
  rw [Function.update_of_ne h109] at hw
  have hp : (SubexpMainNodeInitialization.projected alloc a).stacks i =
      a.stacks (SubexpMainMomentPorts.stackMap alloc i) := rfl
  exact hw.trans hp

theorem nonmaster_empty {er es : ℕ} {alloc : Allocation es}
    {a b : MainState er es} {D : ℕ}
    (h : SubexpMainNodeInitialization.Result alloc
      (SubexpMainNodeSetup.prepared alloc a) b D)
    (i : Fin 288) (hi : ¬ SubexpNodeWorkspace.MasterPort i) :
    workerStacks alloc (SubexpMainNodeScratch.result alloc b) i = [] := by
  have hn := hi
  simp only [SubexpNodeWorkspace.MasterPort, not_or, Fin.ext_iff,
    Fin.coe_ofNat_eq_mod] at hn
  have hlo : i.val < 256 := by omega
  let j : Fin 672 := ⟨i.val, by omega⟩
  have h5 : i.castAdd 64 ≠ (5 : Fin 352) := by
    intro he
    have hv := congrArg (fun q : Fin 352 => q.val) he
    change i.val = 5 at hv
    omega
  have h10 : i.castAdd 64 ≠ (10 : Fin 352) := by
    intro he
    have hv := congrArg (fun q : Fin 352 => q.val) he
    change i.val = 10 at hv
    omega
  have hm : SubexpMainMomentPorts.stackMap alloc (i.castAdd 64) = ordinary alloc j := by
    simp only [SubexpMainMomentPorts.stackMap, ite_eq_right h5, ite_eq_right h10,
      SubexpMainMomentPorts.baseMap, Fin.val_castAdd, dite_eq_left hlo, j]
  change (SubexpMainNodeScratch.result alloc b).stacks
    (SubexpMainMomentPorts.stackMap alloc (i.castAdd 64)) = []
  rw [hm]
  by_cases h243 : i.val = 243
  · have hj : j = 243 := Fin.ext h243
    rw [hj]
    exact SubexpMainNodeScratch.result_cleared alloc b
  · have hscratch : ordinary alloc j ≠ ordinary alloc 243 := by
      intro he
      have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
      exact h243 hv
    rw [SubexpMainNodeScratch.result_frame alloc b _ hscratch]
    have hu (k : Fin 352)
        (hk : k.val = 25 ∨ k.val = 92 ∨ k.val = 109 ∨ k.val = 122 ∨
          k.val = 123 ∨ k.val = 124 ∨ k.val = 125 ∨ k.val = 127) :
        i.castAdd 64 ≠ k := by
      intro he
      have hv := congrArg (fun q : Fin 352 => q.val) he
      change i.val = k.val at hv
      rcases hk with hk | hk | hk | hk | hk | hk | hk | hk <;> omega
    have hf := initializer_frame h (i.castAdd 64)
      (hu 25 (by decide)) (hu 92 (by decide)) (hu 109 (by decide))
      (hu 122 (by decide)) (hu 123 (by decide)) (hu 124 (by decide))
      (hu 125 (by decide)) (hu 127 (by decide))
    rw [hm] at hf
    rw [hf, SubexpMainNodeSetup.prepared_frame alloc a (ordinary alloc j)]
    · apply SubexpMainNodePreclear.result_cleared
      change SubexpMainNodePreclear.Selected i.val
      dsimp [SubexpMainNodePreclear.Selected]
      omega
    · intro he
      have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
      change i.val = 91 at hv
      omega
    · intro he
      have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
      change i.val = 319 at hv
      omega
    · intro k he
      have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
      fin_cases k <;> norm_num [SubexpMainNodeHeader.targetPort, ordinary, j] at hv <;> omega

theorem workspace_ready {er es : ℕ} {alloc : Allocation es}
    {a b : MainState er es} {D : ℕ}
    (h : SubexpMainNodeInitialization.Result alloc
      (SubexpMainNodeSetup.prepared alloc a) b D) :
    let words := workerStacks alloc (SubexpMainNodeScratch.result alloc b)
    SubexpNodeWorkspace.Ready words words := by
  dsimp only
  funext i
  by_cases hi : SubexpNodeWorkspace.MasterPort i
  · exact (SubexpNodeWorkspace.initial_master _ i hi).symm
  · rw [SubexpNodeWorkspace.initial_empty _ i hi]
    exact nonmaster_empty h i hi

theorem outer_empty {er es : ℕ} {alloc : Allocation es}
    {a b : MainState er es} {D : ℕ}
    (h : SubexpMainNodeInitialization.Result alloc
      (SubexpMainNodeSetup.prepared alloc a) b D)
    (i : Fin 352) (hlo : 288 ≤ i.val) (h332 : i ≠ 332) :
    (SubexpMainMoments.projected alloc (SubexpMainNodeScratch.result alloc b)).stacks i = [] := by
  let j : Fin 672 := ⟨i.val - 32, by omega⟩
  have hm : SubexpMainMomentPorts.stackMap alloc i = ordinary alloc j := by
    have h5 : i ≠ 5 := by intro he; subst i; norm_num at hlo
    have h10 : i ≠ 10 := by intro he; subst i; norm_num at hlo
    simp only [SubexpMainMomentPorts.stackMap, ite_eq_right h5, ite_eq_right h10,
      SubexpMainMomentPorts.baseMap, dite_eq_right (by omega : ¬ i.val < 256),
      dite_eq_right (by omega : ¬ i.val < 288), j]
  have hscratch : ordinary alloc j ≠ ordinary alloc 243 := by
    intro he
    have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
    change i.val - 32 = 243 at hv
    omega
  change (SubexpMainNodeScratch.result alloc b).stacks
    (SubexpMainMomentPorts.stackMap alloc i) = []
  rw [hm, SubexpMainNodeScratch.result_frame alloc b _ hscratch]
  have hne (k : Fin 352) (hk : k.val < 288) : i ≠ k := by
    intro he
    have hv := congrArg (fun q : Fin 352 => q.val) he
    omega
  have hf := initializer_frame h i (hne 25 (by decide)) (hne 92 (by decide))
    (hne 109 (by decide)) (hne 122 (by decide)) (hne 123 (by decide))
    (hne 124 (by decide)) (hne 125 (by decide)) (hne 127 (by decide))
  rw [hm] at hf
  rw [hf]
  by_cases h319 : j = 319
  · rw [h319]
    exact SubexpMainNodeReduction.installed_temporary alloc _
  · rw [SubexpMainNodeSetup.prepared_frame alloc a (ordinary alloc j)]
    · apply SubexpMainNodePreclear.result_cleared
      have hi332 : i.val ≠ 332 := by
        intro he
        exact h332 (Fin.ext he)
      change SubexpMainNodePreclear.Selected (i.val - 32)
      dsimp [SubexpMainNodePreclear.Selected]
      omega
    · intro he
      have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
      change i.val - 32 = 91 at hv
      omega
    · intro he
      apply h319
      exact Fin.ext (congrArg (fun q : Fin (totalStacks es) => q.val) he)
    · intro k he
      have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
      fin_cases k <;> norm_num [SubexpMainNodeHeader.targetPort, ordinary, j] at hv <;> omega

theorem collector_ready {er es : ℕ} {alloc : Allocation es}
    {a b : MainState er es} {D : ℕ}
    (h : SubexpMainNodeInitialization.Result alloc
      (SubexpMainNodeSetup.prepared alloc a) b D) :
    let words := workerStacks alloc (SubexpMainNodeScratch.result alloc b)
    SubexpNodeWideLoop.Ready (SubexpNodeWorkspace.Ready words)
      (SubexpMainMoments.projected alloc (SubexpMainNodeScratch.result alloc b)) := by
  refine ⟨workspace_ready h, ?_, ?_, ?_, outer_empty h 337 (by decide) (by decide)⟩
  · exact nonmaster_empty h 78 (by decide)
  · exact nonmaster_empty h 102 (by decide)
  · exact nonmaster_empty h 104 (by decide)

end SubexponentialSAT.SubexpMainMomentReady

end OAI.Algorithms
