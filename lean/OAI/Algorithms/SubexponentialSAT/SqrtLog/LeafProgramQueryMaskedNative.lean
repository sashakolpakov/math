import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryMarkedNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryInitialWidth

namespace OAI.Algorithms

/-! Exact execution of the actual marked or final callback with arbitrary outer
source and accumulator. Their lengths do not enter the preparation certificate. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Carried
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay LeafParametersProgram

private theorem workspace_visible (i : Fin 763) : ¬hidden (Marked.Wide.workPort i) := by
  intro hi
  simp only [hidden,LeafBranchProgram.Wide.outerHidden,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with h|h
  · exact workspace_port_ne i 320 (by decide) (by decide) h
  · exact workspace_port_ne i 322 (by decide) (by decide) h

theorem reference_workspace (a : Data) : Marked.Wide.workspace (reference a)=Marked.Wide.workspace a := by
  funext i
  exact reference_visible a (Marked.Wide.workPort i) (workspace_visible i)

theorem restore_workspace (a b : Data) : Marked.Wide.workspace (restore a b)=Marked.Wide.workspace b := by
  funext i
  change (restore a b).stacks (Marked.Wide.workPort i)=b.stacks (Marked.Wide.workPort i)
  simp [restore,rebaseState,rebaseStacks,workspace_visible i]

theorem restore_visible (a b : Data) (i : Fin 768) (hi : ¬hidden i) :
    (restore a b).stacks i=b.stacks i := by
  simp [restore,rebaseState,rebaseStacks,hi]

theorem restore_hidden (a b : Data) (i : Fin 768) (hi : hidden i) :
    (restore a b).stacks i=a.stacks i := by
  simp [restore,rebaseState,rebaseStacks,hi]

theorem marked_from_masked_preparation (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hg : Guard (q.input k)) (W V L : ℕ)
    (p : Preparation q k (markedInput (reference a)) hg W V L) (hc : CleanWork a)
    (hw : ∀i,((markedInput (reference a)).stacks i).length ≤ W) (count B width : ℕ)
    (ctx : Marked.Wide.BranchContext Residual.command (Marked.Wide.maskCopied (prepared p.out))
      (ProtectedWork (reference a)) count B width) :
    ∃n b, n ≤ 10*(a.stacks 321).length+10+preparationBudget p B ∧
      Eval (marked k) n a b ∧ Marked.Wide.workspace b=Marked.Wide.workspace a ∧
      b.stacks 320=a.stacks 320 ∧ b.stacks 322=a.stacks 322 ∧
      BinaryArithmetic.toNat (b.stacks 323)=count ∧ (b.stacks 323).length ≤ width ∧
      b.regs 16=false ∧ b.regs 17=true ∧ b.regs 18=false ∧
      b.stacks 321=[] ∧ b.stacks 324=[] := by
  obtain ⟨n,b,hn,he,hs,h320,h322,hv,hl,h16,h17,h18,h321,h324⟩ :=
    marked_from_preparation q k (reference a) hg W V L p (reference_clean a hc) hw count B width ctx
  rw [reference_visible a 321 (by decide)] at hn
  refine ⟨n,restore a b,hn,marked_replay k a b he,?_,
    restore_hidden a b 320 (by decide),restore_hidden a b 322 (by decide),?_,?_,h16,h17,h18,?_,?_⟩
  · exact (restore_workspace a b).trans (hs.trans (reference_workspace a))
  · simpa only [restore_visible a b 323 (by decide)] using hv
  · simpa only [restore_visible a b 323 (by decide)] using hl
  · exact (restore_visible a b 321 (by decide)).trans h321
  · exact (restore_visible a b 324 (by decide)).trans h324

theorem accepted_from_masked_preparation (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hg : Guard (q.input k)) (W V L : ℕ)
    (p : Preparation q k (unmarkedInput (reference a)) hg W V L) (hc : CleanWork a)
    (hw : ∀i,((unmarkedInput (reference a)).stacks i).length ≤ W) (count B width : ℕ)
    (ctx : Marked.Wide.BranchContext Residual.command (Marked.Wide.maskCopied (prepared p.out))
      (ProtectedWork (reference a)) count B width) :
    ∃n b, n ≤ 3+preparationBudget p B ∧
      Eval (accepted k) n a b ∧ Marked.Wide.workspace b=Marked.Wide.workspace a ∧
      b.stacks 320=a.stacks 320 ∧ b.stacks 322=a.stacks 322 ∧
      BinaryArithmetic.toNat (b.stacks 323)=count ∧ (b.stacks 323).length ≤ width ∧
      b.regs 16=false ∧ b.regs 17=true ∧ b.regs 18=false ∧
      b.stacks 321=[] ∧ b.stacks 324=[] := by
  obtain ⟨n,b,hn,he,hs,h320,h322,hv,hl,h16,h17,h18,h321,h324⟩ :=
    accepted_from_preparation q k (reference a) hg W V L p (reference_clean a hc) hw count B width ctx
  refine ⟨n,restore a b,hn,accepted_replay k a b he,?_,
    restore_hidden a b 320 (by decide),restore_hidden a b 322 (by decide),?_,?_,h16,h17,h18,?_,?_⟩
  · exact (restore_workspace a b).trans (hs.trans (reference_workspace a))
  · simpa only [restore_visible a b 323 (by decide)] using hv
  · simpa only [restore_visible a b 323 (by decide)] using hl
  · exact (restore_visible a b 321 (by decide)).trans h321
  · exact (restore_visible a b 324 (by decide)).trans h324

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Carried

end OAI.Algorithms
