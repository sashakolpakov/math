import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookupLocal

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 340

def stack : Fin 12 → Fin 340 := ![233,212,216,337,304,315,316,317,318,319,338,339]
theorem stack_injective : Function.Injective stack := by decide

def Clean (d : Data) : Prop :=
  ∀ i ∈ ([304,315,316,317,318,319,338,339] : List (Fin 340)), d.stacks i=[]

abbrev command : Cmd 16 340 := liftCommand Local.command 0 4 id stack

def budget (d : Data) (nodes : List (List Bool)) : ℕ :=
  Local.budget (d.stacks 233) (d.stacks 212) (d.stacks 216) nodes+1

/-- The physical search preserves every stack except its designated row output. -/
theorem command_eval (d : Data) (nodes : List (List Bool))
    (hmaster : d.stacks 337=ProgramEncoding.encodeRecords nodes) (hclean : Clean d) :
    ∃ n ≤ budget d nodes, ∃ e : Data,
      Eval command n d e ∧
      e.stacks=Function.update d.stacks 304
        (List.replicate (nodes.idxOf
          (pairKey (d.stacks 233) (d.stacks 212++d.stacks 216))) true) := by
  have h304 := hclean 304 (by simp)
  have h315 := hclean 315 (by simp)
  have h316 := hclean 316 (by simp)
  have h317 := hclean 317 (by simp)
  have h318 := hclean 318 (by simp)
  have h319 := hclean 319 (by simp)
  have h338 := hclean 338 (by simp)
  have h339 := hclean 339 (by simp)
  obtain ⟨n,hn,rs,he⟩ := Local.command_eval d.regs
    (d.stacks 233) (d.stacks 212) (d.stacks 216) nodes
  have ha : projectState id stack d =
      data d.regs (d.stacks 233) (d.stacks 212) (d.stacks 216)
        (ProgramEncoding.encodeRecords nodes) [] [] [] [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;>
        simp [projectState,stack,data,hmaster,h304,h315,h316,h317,h318,h319,h338,h339]
  rw [←ha] at he
  have hh := eval_liftCommand_from_state Local.command 0 4 id stack d
    Function.injective_id stack_injective he
  let count := List.replicate (nodes.idxOf
    (pairKey (d.stacks 233) (d.stacks 212++d.stacks 216))) true
  let e := embedState id stack d
    (data rs (d.stacks 233) (d.stacks 212) (d.stacks 216)
      (ProgramEncoding.encodeRecords nodes) count [] [] [] [] [] [] [])
  refine ⟨n+1,Nat.add_le_add_right hn 1,e,hh,?_⟩
  funext j
  by_cases hj : ∃ i, stack i=j
  · obtain ⟨i,rfl⟩ := hj
    rw [show e.stacks (stack i)=_ from embedState_stack id stack d _ stack_injective i]
    fin_cases i <;>
      simp [stack,data,count,hmaster,h315,h316,h317,h318,h319,h338,h339]
  · have hj304 : j≠304 := fun h => hj ⟨4,by simpa [stack] using h.symm⟩
    rw [Function.update_of_ne hj304]
    exact embedState_stack_frame id stack d _ j hj

def program := compiled command 233 304

theorem program_run (d : Data) (nodes : List (List Bool))
    (hmaster : d.stacks 337=ProgramEncoding.encodeRecords nodes) (hclean : Clean d) :
    ∃ e : Data,
      RunsIn program (budget d nodes+1) (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks=Function.update d.stacks 304
        (List.replicate (nodes.idxOf
          (pairKey (d.stacks 233) (d.stacks 212++d.stacks 216))) true) := by
  obtain ⟨n,hn,e,he,hs⟩ := command_eval d nodes hmaster hclean
  exact ⟨e,⟨n+1,Nat.add_le_add_right hn 1,compiled_halt_trace he 233 304⟩,hs⟩

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native

end OAI.Algorithms
