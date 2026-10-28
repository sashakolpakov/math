import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramEntryBankFrameCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramEntryBankFrameLookup

namespace OAI.Algorithms

/-! Measured staging and exact caller-store frames for the fixed source bank. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem stageTypes_temp (a : Data) (ht : a.stacks 319=[]) :
    (Staging.result 0 1 stageTypesOps a).stacks 319=[] :=
  EntryBankFrame.staging_result_temp 0 1 319 stageTypesOps a stageTypes_valid ht

theorem stageEmitter_temp (a : Data) (ht : a.stacks 319=[]) :
    (Staging.result 0 1 stageEmitterOps a).stacks 319=[] :=
  EntryBankFrame.staging_result_temp 0 1 319 stageEmitterOps a stageEmitter_valid ht

theorem stageTypes_stacks (a : Data) (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[]) :
    (Staging.result 0 1 stageTypesOps a).stacks=
      Function.update (Function.update a.stacks 23 (a.stacks 289)) 24 (a.stacks 292) := by
  simp [stageTypesOps,Staging.result,Staging.actionResult,StackRoutines.copyStacks,h23,h24]

theorem stageTypes_cost (a : Data) : Staging.cost 0 1 stageTypesOps a=
    7*((a.stacks 289).length+(a.stacks 292).length)+10 := by
  simp [stageTypesOps,Staging.cost,Staging.actionCost,Staging.actionResult,StackRoutines.copyStacks]
  ring

def emitterDestinations : List (Fin 320) := [280,281,282,283,284,285,286,259,266,269]
def emitterSize (a : Data) : ℕ :=
  (a.stacks 67).length+(a.stacks 308).length+(a.stacks 309).length+
  (a.stacks 310).length+(a.stacks 71).length+(a.stacks 311).length+
  (a.stacks 312).length+(a.stacks 313).length+(a.stacks 314).length+(a.stacks 47).length

def emitterStacks (a : Data) : Fin 320 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update a.stacks 280 (a.stacks 67)) 281 (a.stacks 308))
    282 (a.stacks 309)) 283 (a.stacks 310)) 284 (a.stacks 71)) 285 (a.stacks 311))
    286 (a.stacks 312)) 259 (a.stacks 313)) 266 (a.stacks 314)) 269 (a.stacks 47)

theorem stageEmitter_stacks (a : Data)
    (h : ∀ j∈emitterDestinations,a.stacks j=[]) :
    (Staging.result 0 1 stageEmitterOps a).stacks=emitterStacks a := by
  have h280 := h 280 (by simp [emitterDestinations])
  have h281 := h 281 (by simp [emitterDestinations])
  have h282 := h 282 (by simp [emitterDestinations])
  have h283 := h 283 (by simp [emitterDestinations])
  have h284 := h 284 (by simp [emitterDestinations])
  have h285 := h 285 (by simp [emitterDestinations])
  have h286 := h 286 (by simp [emitterDestinations])
  have h259 := h 259 (by simp [emitterDestinations])
  have h266 := h 266 (by simp [emitterDestinations])
  have h269 := h 269 (by simp [emitterDestinations])
  simp [stageEmitterOps,Staging.result,Staging.actionResult,StackRoutines.copyStacks,
    emitterStacks,h280,h281,h282,h283,h284,h285,h286,h259,h266,h269]

theorem stageEmitter_cost (a : Data) :
    Staging.cost 0 1 stageEmitterOps a=7*emitterSize a+50 := by
  simp [stageEmitterOps,Staging.cost,Staging.actionCost,Staging.actionResult,
    StackRoutines.copyStacks,emitterSize]
  ring

theorem stageEmitter_frame (a : Data) (j : Fin 320) (hj : j∉emitterDestinations) :
    (Staging.result 0 1 stageEmitterOps a).stacks j=a.stacks j := by
  apply Staging.result_frame
  intro op hop
  simp only [stageEmitterOps,List.mem_cons,List.not_mem_nil,or_false] at hop
  rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp_all [Staging.Action.destination,emitterDestinations]

theorem cleanup_valid : ∀ op∈cleanupOps,op.Valid (319:Fin 320) := by
  intro op hop
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
  trivial

theorem cleanup_eval (a : Data) (ht : a.stacks 319=[]) :
    Eval cleanup (Staging.cost 0 1 cleanupOps a) a (Staging.result 0 1 cleanupOps a) :=
  Staging.sequence_eval 0 1 319 (by decide) cleanupOps a cleanup_valid ht

theorem cleanup_stacks (a : Data) (j : Fin 320) :
    (Staging.result 0 1 cleanupOps a).stacks j=
      if j∈cleanupPorts then [] else a.stacks j :=
  Staging.result_clears 0 1 cleanupPorts a j

theorem cleanup_cost (a : Data) :
    Staging.cost 0 1 cleanupOps a ≤
      2*(cleanupPorts.map (fun j => (a.stacks j).length)).sum+180 := by
  simpa [cleanupOps,cleanupPorts] using EntryBankFrame.clear_cost_le 0 1 cleanupPorts a

theorem cleanup_cost_le (a : Data) (B : ℕ)
    (h : ∀ j∈cleanupPorts,(a.stacks j).length ≤ B) :
    Staging.cost 0 1 cleanupOps a ≤ 120*B+180 := by
  have hs := EntryBankFrame.sum_map_le_length cleanupPorts (fun j => (a.stacks j).length) B h
  have hc := cleanup_cost a
  have hl : cleanupPorts.length=60 := by simp [cleanupPorts]
  rw [hl] at hs
  omega

theorem cleanup_frame (a : Data) (j : Fin 320) (hj : j∉cleanupPorts) :
    (Staging.result 0 1 cleanupOps a).stacks j=a.stacks j := by
  rw [cleanup_stacks,ite_eq_right hj]

theorem cleanup_temp (a : Data) (ht : a.stacks 319=[]) :
    (Staging.result 0 1 cleanupOps a).stacks 319=[] :=
  EntryBankFrame.staging_result_temp 0 1 319 cleanupOps a cleanup_valid ht

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
