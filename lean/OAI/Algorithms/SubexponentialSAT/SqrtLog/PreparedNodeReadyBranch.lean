import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PreparedNodeReady

namespace OAI.Algorithms

/-! Readiness at the concrete high-branch collector boundary. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram LeafHeadSetupProgram
variable {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data} {hg : Guard (q.input k)}
  {W V L : ℕ} (p : Query.Preparation q k a hg W V L)

def branch (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool) : Data :=
  let b := Marked.Wide.maskCopied (Query.prepared p.out)
  LeafHighContextProgram.finished ⟨b.regs,Function.update b.stacks 330 counter⟩ regs high

theorem branch_parked (node : Fin (Query.packingProblem q k hg).Q)
    (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool) :
    Parked (Native.queryInputsAddressed q k hg p.firstWord p.remainingWords node)
      (branch p counter regs high) :=
  parked_highContext (parked_setCounter (prepared_parked p node) counter) regs high

theorem branch_blank_of_low (hb : NodeNative.Blank a)
    (hlow : ∀ i : Fin 768,i.val < 190 → p.packed.stacks i=[] → p.out.stacks i=[])
    (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool) :
    NodeNative.Blank (branch p counter regs high) :=
  highContext_blank (setCounter_blank (prepared_blank_of_low p hb hlow) counter) regs high

theorem collector_ready_of_low (hb : NodeNative.Blank a)
    (hlow : ∀ i : Fin 768,i.val < 190 → p.packed.stacks i=[] → p.out.stacks i=[])
    (node : Fin (Query.packingProblem q k hg).Q)
    (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool)
    (rr : Fin 40 → Bool) (store : LeafNodeSamplesProgram.Store)
    (hf : store.frame=(branch p counter regs high).stacks)
    (hn : store.index=unary node.val) (hs : store.shape=[]) :
    NodeNative.Ready (Native.queryInputsAddressed q k hg p.firstWord p.remainingWords node)
      (LeafNodeSamplesProgram.state rr store) := by
  apply collector_ready _ rr store _ _ hn hs
  · apply (branch_parked p node counter regs high).congr
    intro i _ _
    exact congrFun hf i
  · intro i hi hn'
    change store.frame i=[]
    rw [hf]
    exact branch_blank_of_low p hb hlow counter regs high i hi hn'
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady

end

end OAI.Algorithms
