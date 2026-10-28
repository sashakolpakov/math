import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafMarkedProgramWideNative

namespace OAI.Algorithms

/-! Reclamation restores the marked collector's entire reusable workspace.
The computed answer on323 is deliberately outside that workspace. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls

theorem workspace_port_ne (i : Fin 763) (j : Fin 768)
    (hlo : 320 ≤ j.val) (hhi : j.val ≤ 324) : Marked.Wide.workPort i≠j := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [Marked.Wide.workPort] at hv
  split_ifs at hv <;> simp only at hv <;> omega

theorem cleanup_restores_workspace (a b : Data) (hc : CleanWork a)
    (hf : ∀i,Protected i → i≠323 → b.stacks i=a.stacks i) :
    Marked.Wide.workspace (cleaned b)=Marked.Wide.workspace a := by
  funext i
  change (cleaned b).stacks (Marked.Wide.workPort i)=a.stacks (Marked.Wide.workPort i)
  by_cases hp : Protected (Marked.Wide.workPort i)
  · exact (cleaned_frame b _ hp).trans
      (hf _ hp (workspace_port_ne i 323 (by decide) (by decide)))
  · rw [cleaned_empty b _ hp]
    exact (hc _ hp (workspace_port_ne i 321 (by decide) (by decide))).symm

theorem cleanup_preserves_ready (ready : (Fin 763 → List Bool) → Prop) (a b : Data)
    (ha : ready (Marked.Wide.workspace a)) (hc : CleanWork a)
    (hf : ∀i,Protected i → i≠323 → b.stacks i=a.stacks i) :
    ready (Marked.Wide.workspace (cleaned b)) := by
  rw [cleanup_restores_workspace a b hc hf]
  exact ha

theorem markedInput_sources (q : LeafQueryFrontend.Query) (a : Data) (h : Sources q a) :
    Sources q (markedInput a) := by
  constructor
  · exact (markedInput_frame a 700 (by decide) (by decide) (by decide)).trans h.formula
  · exact (markedInput_frame a 701 (by decide) (by decide) (by decide)).trans h.rows
  · exact (markedInput_frame a 707 (by decide) (by decide) (by decide)).trans h.modulus
  · exact (markedInput_frame a 708 (by decide) (by decide) (by decide)).trans h.width
  · exact (markedInput_frame a 709 (by decide) (by decide) (by decide)).trans h.ambient

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
