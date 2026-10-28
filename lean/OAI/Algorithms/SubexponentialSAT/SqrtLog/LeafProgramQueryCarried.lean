import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryReference
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryBranches
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramCountPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgramWideReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramOuterCarriedMono
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayMacros

namespace OAI.Algorithms

/-! The per-query caller may carry arbitrary outer source and mass streams.
Neither is read or written by the query. The branch mass332 remains visible. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Carried
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay

abbrev hidden := LeafBranchProgram.Wide.outerHidden

private theorem countPrepare_320 : (320 : Fin 768) ∉ Count.Prepare.ports :=
  Count.Prepare.ports_gap 320 (by norm_num) (by norm_num)
private theorem countPrepare_322 : (322 : Fin 768) ∉ Count.Prepare.ports :=
  Count.Prepare.ports_gap 322 (by norm_num) (by norm_num)

attribute [local irreducible] cleanupPorts Count.Prepare.ports

theorem subset (i : Fin 768) (hi : hidden i) : OuterCarried.hidden i := by
  simp only [hidden,LeafBranchProgram.Wide.outerHidden,OuterCarried.hidden,
    List.mem_cons,List.not_mem_nil,or_false] at *
  rcases hi with h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem hidden_protected (i : Fin 768) (hi : hidden i) : Protected i := by
  simp only [hidden,LeafBranchProgram.Wide.outerHidden,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl <;> decide

theorem clearBank (ps : List (Fin 768)) (hp : ∀i∈ps,¬hidden i) :
    AvoidsCmd hidden (BankRoutines.clearCmd 699 (0 : Fin 40) 1 ps) := by
  induction ps with
  | nil => exact avoids_clearProgram hidden 699 0 1 (by decide)
  | cons i ps ih =>
    exact ⟨avoids_clearProgram hidden i 0 1 (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

theorem cleanupBank_avoids :
    AvoidsCmd hidden (BankRoutines.clearCmd 699 (0 : Fin 40) 1 cleanupPorts) :=
  clearBank cleanupPorts fun i hi hh =>
    ((mem_cleanupPorts i).mp hi).1 (hidden_protected i hh)

theorem cleanup_avoids : AvoidsCmd hidden cleanup := by
  constructor
  · exact avoids_clearProgram hidden 699 0 1 (by decide)
  · exact cleanupBank_avoids

theorem markInput_avoids : AvoidsCmd hidden markInput := by
  constructor
  · exact avoids_copyProgram hidden 321 699 698 0 1 (by decide) (by decide) (by decide)
  · constructor
    · exact avoids_transferProgram hidden 699 705 0 1 (by decide) (by decide)
    · constructor
      · trivial
      · constructor
        · change ¬hidden _
          decide
        · trivial

theorem noMarkInput_avoids : AvoidsCmd hidden noMarkInput := by
  constructor
  · trivial
  · constructor
    · change ¬hidden _
      decide
    · constructor
      · change ¬hidden _
        decide
      · trivial

theorem countPrepareBank_avoids :
    AvoidsCmd hidden (BankRoutines.clearCmd 699 (0 : Fin 40) 1 Count.Prepare.ports) :=
  clearBank Count.Prepare.ports fun i hi hh => by
    simp only [hidden, LeafBranchProgram.Wide.outerHidden, List.mem_cons,
      List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl
    · exact countPrepare_320 hi
    · exact countPrepare_322 hi

theorem countPrepare_avoids : AvoidsCmd hidden Count.Prepare.command := by
  constructor
  · exact avoids_clearProgram hidden 699 0 1 (by decide)
  · exact countPrepareBank_avoids

theorem maskCopy_avoids : AvoidsCmd hidden Marked.Wide.maskCopy :=
  avoids_copyProgram hidden 338 333 339 0 1 (by decide) (by decide) (by decide)

theorem branches_avoids (residual : Code) (hr : AvoidsCmd hidden residual) :
    AvoidsCmd hidden (branches residual) :=
  ⟨⟨maskCopy_avoids,LeafBranchProgram.Wide.command_avoids_outer residual hr⟩,cleanup_avoids⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Carried

end OAI.Algorithms
