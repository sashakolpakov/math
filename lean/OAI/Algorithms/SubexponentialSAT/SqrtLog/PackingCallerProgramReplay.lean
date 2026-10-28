import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramOuterCarried
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayMacros

namespace OAI.Algorithms

/-! The native packing caller neither reads nor writes the outer carried
tapes. Their contents therefore do not affect its exact running time. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Replay
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
open LeafProgram.OuterCarried
attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem away (i : Fin 768) (hi : i.val < 320 ∨ 332 < i.val) : ¬ LeafProgram.OuterCarried.hidden i := by
  intro hh
  simp only [LeafProgram.OuterCarried.hidden,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl|rfl|rfl  <;>  norm_num at hi

private theorem bank_away (i : Fin 64) : ¬ LeafProgram.OuterCarried.hidden (Wide.ports i) :=
  away _ (Or.inr (by change 332 < 417+i.val; omega))

private theorem low_away (i : Fin 14) : ¬ LeafProgram.OuterCarried.hidden (LeafProgram.LayoutMasters.low i) :=
  away _ (Or.inl (by change 128+i.val < 320; have := i.isLt; omega))

private theorem high_away (i : Fin 14) : ¬ LeafProgram.OuterCarried.hidden (LeafProgram.LayoutMasters.high i) :=
  away _ (Or.inr (by change 332 < 730+i.val; omega))

private theorem wideCall_avoids (c : Cmd 16 768) (hc : AvoidsCmd LeafProgram.OuterCarried.hidden c) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (Wide.call c) :=
  avoids_liftProgram LeafProgram.OuterCarried.hidden _ _ _ (avoids_compiled LeafProgram.OuterCarried.hidden c hc 684 133)

private theorem stage_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden Wide.stage := by
  apply wideCall_avoids
  apply avoids_copyMany LeafProgram.OuterCarried.hidden 684 Wide.stagePairs (away _ (by norm_num))
  intro p hp
  simp only [Wide.stagePairs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl  <;>
    exact ⟨away _ (by norm_num),bank_away _⟩

private theorem export_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden Wide.exportLocal := by
  constructor
  · apply avoids_copyMany LeafProgram.OuterCarried.hidden 684 Wide.exportPairs (away _ (by norm_num))
    intro p hp
    simp only [Wide.exportPairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl  <;>  exact ⟨bank_away _,away _ (by norm_num)⟩
  · apply avoids_clearMany
    intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact bank_away i

private theorem park_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden LeafProgram.LayoutMasters.parkLocal := by
  constructor
  · apply avoids_copyMany LeafProgram.OuterCarried.hidden 684 LeafProgram.LayoutMasters.parkPairs (away _ (by norm_num))
    intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact ⟨low_away i,high_away i⟩
  · apply avoids_clearMany
    intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact low_away i

theorem command_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden PackingCallerProgram.command := by
  refine ⟨⟨stage_avoids,?_⟩,wideCall_avoids _ ⟨export_avoids,park_avoids⟩⟩
  exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden coreProgram Wide.registers Wide.ports bank_away

theorem program_avoids : AvoidsProgram LeafProgram.OuterCarried.hidden PackingCallerProgram.program :=
  avoids_compiled LeafProgram.OuterCarried.hidden PackingCallerProgram.command command_avoids 718 735

theorem replay {n : ℕ} {a b : Wide.Data} (h : Eval PackingCallerProgram.command n a b)
    (frame : Fin 768 → List Bool) :
    Eval PackingCallerProgram.command n (rebaseState LeafProgram.OuterCarried.hidden frame a) (rebaseState LeafProgram.OuterCarried.hidden frame b) :=
  eval_rebase LeafProgram.OuterCarried.hidden command_avoids h frame

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Replay

#print axioms SubexponentialSAT.SqrtLog.PackingCallerProgram.Replay.command_avoids
#print axioms SubexponentialSAT.SqrtLog.PackingCallerProgram.Replay.replay

end OAI.Algorithms
