import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryEntry

namespace OAI.Algorithms

/-! Paid reference staging is part of every marked query invocation. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

def preparationBudget {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Preparation q k a hg W V L) (B : ℕ) : ℕ :=
  p.frontSteps+p.packingSteps+p.arithmeticSteps+prepareCost p.out+
    branchBudget (prepared p.out) B
      (W+p.frontSteps+p.packingSteps+p.arithmeticSteps+prepareCost p.out)+1

theorem marked_from_preparation (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hg : Guard (q.input k)) (W V L : ℕ)
    (p : Preparation q k (markedInput a) hg W V L) (hc : CleanWork a)
    (hw : ∀i,((markedInput a).stacks i).length ≤ W) (count B width : ℕ)
    (ctx : Marked.Wide.BranchContext Residual.command (Marked.Wide.maskCopied (prepared p.out))
      (ProtectedWork a) count B width) :
    ∃n b, n ≤ 10*(a.stacks 321).length+10+preparationBudget p B ∧
      Eval (marked k) n a b ∧ Marked.Wide.workspace b=Marked.Wide.workspace a ∧
      b.stacks 320=a.stacks 320 ∧ b.stacks 322=a.stacks 322 ∧
      BinaryArithmetic.toNat (b.stacks 323)=count ∧ (b.stacks 323).length ≤ width ∧
      b.regs 16=false ∧ b.regs 17=true ∧ b.regs 18=false ∧
      b.stacks 321=[] ∧ b.stacks 324=[] := by
  have h339 : (markedInput a).stacks 339=[] :=
    (markedInput_frame a 339 (by decide) (by decide) (by decide)).trans
      (hc 339 (by decide) (by decide))
  obtain ⟨n,b,hn,he,hs,h320,h322,hv,hl,h16,h17,h18,h321,h324⟩ :=
    command_from_preparation q k a (markedInput a) hg W V L p hc
      (markedInput_frame a 320 (by decide) (by decide) (by decide))
      (markedInput_frame a 322 (by decide) (by decide) (by decide)) h339 hw count B width ctx
  have hi := markInput_eval a (hc 698 (by decide) (by decide)) (hc 699 (by decide) (by decide))
  exact ⟨10*(a.stacks 321).length+10+n,b,Nat.add_le_add_left hn _,hi.seq he,
    hs,h320,h322,hv,hl,h16,h17,h18,h321,h324⟩

theorem accepted_from_preparation (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hg : Guard (q.input k)) (W V L : ℕ)
    (p : Preparation q k (unmarkedInput a) hg W V L) (hc : CleanWork a)
    (hw : ∀i,((unmarkedInput a).stacks i).length ≤ W) (count B width : ℕ)
    (ctx : Marked.Wide.BranchContext Residual.command (Marked.Wide.maskCopied (prepared p.out))
      (ProtectedWork a) count B width) :
    ∃n b, n ≤ 3+preparationBudget p B ∧
      Eval (accepted k) n a b ∧ Marked.Wide.workspace b=Marked.Wide.workspace a ∧
      b.stacks 320=a.stacks 320 ∧ b.stacks 322=a.stacks 322 ∧
      BinaryArithmetic.toNat (b.stacks 323)=count ∧ (b.stacks 323).length ≤ width ∧
      b.regs 16=false ∧ b.regs 17=true ∧ b.regs 18=false ∧
      b.stacks 321=[] ∧ b.stacks 324=[] := by
  have h339 : (unmarkedInput a).stacks 339=[] :=
    (unmarkedInput_frame a 339 (by decide) (by decide)).trans
      (hc 339 (by decide) (by decide))
  obtain ⟨n,b,hn,he,hs,h320,h322,hv,hl,h16,h17,h18,h321,h324⟩ :=
    command_from_preparation q k a (unmarkedInput a) hg W V L p hc
      (unmarkedInput_frame a 320 (by decide) (by decide))
      (unmarkedInput_frame a 322 (by decide) (by decide)) h339 hw count B width ctx
  exact ⟨3+n,b,Nat.add_le_add_left hn _,(noMarkInput_eval a).seq he,
    hs,h320,h322,hv,hl,h16,h17,h18,h321,h324⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
