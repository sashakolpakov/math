import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgramWideControl
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayFootprint

namespace OAI.Algorithms

/-! Syntactic no-read/no-write footprint of the genuine wide branch controller. -/
namespace SubexponentialSAT.SqrtLog.LeafBranchProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls ProgramTapeReplay

/-- These are controller tapes, including the live branch accumulator332. -/
def controlTapes : List (Fin 768) := [321,323,324,330,331,332,333]

private theorem init_avoids (H : Fin 768 → Prop)
    (hp : ∀ i ∈ controlTapes, ¬ H i) : AvoidsCmd H initCommand := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i
  · exact hp 333 (by simp [controlTapes])
  · exact hp 330 (by simp [controlTapes])

private theorem mass_avoids (H : Fin 768 → Prop)
    (hp : ∀ i ∈ controlTapes, ¬ H i) :
    AvoidsCmd H (LeafProgram.Mass.invoke fixedPorts.mass) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i
  · exact hp 332 (by simp [controlTapes])
  · exact hp 323 (by simp [controlTapes])
  · exact hp 324 (by simp [controlTapes])

private theorem increment_avoids (H : Fin 768 → Prop)
    (hp : ∀ i ∈ controlTapes, ¬ H i) :
    AvoidsCmd H (ExecCNFTupleEnumeration.incrementCmd fixedPorts.counter) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i
  · exact hp 330 (by simp [controlTapes])
  · exact hp 331 (by simp [controlTapes])

private theorem finish_avoids (H : Fin 768 → Prop)
    (hp : ∀ i ∈ controlTapes, ¬ H i) : AvoidsCmd H finish := by
  have h330 := avoids_clearProgram H (330 : Fin 768) (0 : Fin 40) 1
    (hp 330 (by simp [controlTapes]))
  have h321 := avoids_clearProgram H (321 : Fin 768) (0 : Fin 40) 1
    (hp 321 (by simp [controlTapes]))
  have h332 := avoids_transferProgram H (332 : Fin 768) 324 (0 : Fin 40) 1
    (hp 332 (by simp [controlTapes])) (hp 324 (by simp [controlTapes]))
  have h324 := avoids_transferProgram H (324 : Fin 768) 323 (0 : Fin 40) 1
    (hp 324 (by simp [controlTapes])) (hp 323 (by simp [controlTapes]))
  exact ⟨h330,⟨⟨h332,h324⟩,⟨h321,⟨trivial,⟨trivial,trivial⟩⟩⟩⟩⟩

/-- Hiding a disjoint caller frame is compatible with the actual initializer,
all-visits odometer, live accumulator, and final cleanup. -/
theorem command_avoids (H : Fin 768 → Prop) (query : Code)
    (hp : ∀ i ∈ controlTapes, ¬ H i) (hq : AvoidsCmd H query) :
    AvoidsCmd H (command query) := by
  have hb : AvoidsCmd H (body fixedPorts query) := ⟨hq,mass_avoids H hp⟩
  have ha : AvoidsCmd H (ExecCNFTupleEnumeration.advanceCmd fixedPorts.counter) :=
    ⟨increment_avoids H hp,trivial⟩
  have he : AvoidsCmd H (ExecCNFTupleEnumeration.enumerate fixedPorts.counter
      (body fixedPorts query)) := ⟨trivial,⟨hb,ha⟩⟩
  exact ⟨init_avoids H hp,⟨he,finish_avoids H hp⟩⟩

theorem program_avoids (H : Fin 768 → Prop) (query : Code)
    (hp : ∀ i ∈ controlTapes, ¬ H i) (hq : AvoidsCmd H query) :
    AvoidsProgram H (program query) :=
  avoids_compiled H (command query) (command_avoids H query hp hq) 333 323

/-- Only the caller's source and outer mass are hidden; branch mass332 is live. -/
def outerHidden (i : Fin 768) : Prop := i ∈ ([320,322] : List (Fin 768))
instance outerHidden_decidable : DecidablePred outerHidden := by
  intro i
  unfold outerHidden
  infer_instance

theorem controlTapes_visible : ∀ i ∈ controlTapes, ¬ outerHidden i := by
  intro i hi
  simp only [controlTapes,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem command_avoids_outer (query : Code) (hq : AvoidsCmd outerHidden query) :
    AvoidsCmd outerHidden (command query) :=
  command_avoids outerHidden query controlTapes_visible hq

/-- The complete branch query replays in exactly the same number of steps. -/
theorem command_rebase_outer (query : Code) (hq : AvoidsCmd outerHidden query)
    {n : ℕ} {a b : Data} (he : Eval (command query) n a b)
    (frame : Fin 768 → List Bool) :
    Eval (command query) n (rebaseState outerHidden frame a)
      (rebaseState outerHidden frame b) :=
  eval_rebase outerHidden (command_avoids_outer query hq) he frame

end SubexponentialSAT.SqrtLog.LeafBranchProgram.Wide

end OAI.Algorithms
