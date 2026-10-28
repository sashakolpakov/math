import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramInterpolation
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayMacros
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramOuterCarried

namespace OAI.Algorithms

/-! Exact-time replay footprint of the existing interpolation producer. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.Replay
open BitProgram StructuredCalls ProgramTapeReplay

theorem visible (i : Fin 768) (h : i.val < 320 ∨ 340 ≤ i.val) : ¬LeafProgram.OuterCarried.hidden i := by
  intro hh
  have hv : i.val=320 ∨ i.val=322 ∨ i.val=332 := by
    simpa [LeafProgram.OuterCarried.hidden,Fin.ext_iff] using hh
  omega

theorem clear (i : Fin 768) (h : ¬LeafProgram.OuterCarried.hidden i) : AvoidsCmd LeafProgram.OuterCarried.hidden (Interpolation.clear i) :=
  avoids_clearProgram LeafProgram.OuterCarried.hidden i 38 39 h

theorem copy (src dst : Fin 768) (hs : ¬LeafProgram.OuterCarried.hidden src) (hd : ¬LeafProgram.OuterCarried.hidden dst) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (Interpolation.copy src dst) :=
  avoids_copyProgram LeafProgram.OuterCarried.hidden src dst 699 38 39 hs hd (by decide)

theorem overwrite (src dst : Fin 768) (hs : ¬LeafProgram.OuterCarried.hidden src) (hd : ¬LeafProgram.OuterCarried.hidden dst) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (Interpolation.overwrite src dst) := ⟨clear dst hd,copy src dst hs hd⟩

theorem clearPorts (ps : List (Fin 768)) (hp : ∀i∈ps,¬LeafProgram.OuterCarried.hidden i) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (Interpolation.clearPorts ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact ⟨clear p (hp p (by simp)),ih (fun i hi => hp i (by simp [hi]))⟩

theorem copyPlan (ps : List (Fin 768 × Fin 768))
    (hp : ∀p∈ps,¬LeafProgram.OuterCarried.hidden p.1 ∧ ¬LeafProgram.OuterCarried.hidden p.2) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (Interpolation.copyPlan ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact ⟨overwrite p.1 p.2 (hp p (by simp)).1 (hp p (by simp)).2,
      ih (fun q hq => hp q (by simp [hq]))⟩

theorem private_visible : ∀i∈privatePorts,¬LeafProgram.OuterCarried.hidden i := by
  intro i hi
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
  apply visible
  right
  change 340 ≤ 340+j.val
  omega

theorem command_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden Interpolation.command := by
  have hc : AvoidsCmd LeafProgram.OuterCarried.hidden coreCall := by
    apply avoids_call_lift_of_range
    intro i
    apply visible
    right
    change 340 ≤ 340+i.val
    omega
  have hi : AvoidsCmd LeafProgram.OuterCarried.hidden (Interpolation.copyPlan inputPlan) := copyPlan _ (by
    intro p hp
    simp only [inputPlan,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
  have ho : AvoidsCmd LeafProgram.OuterCarried.hidden (Interpolation.copyPlan outputPlan) := copyPlan _ (by
    intro p hp
    simp only [outputPlan,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl <;> decide)
  exact ⟨clearPorts _ (by
    intro i hi
    rcases List.mem_cons.mp hi with rfl|hi
    · decide
    · exact private_visible i hi),hi,hc,ho,clearPorts _ private_visible⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.Replay

end OAI.Algorithms
