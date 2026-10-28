import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PreparedNodeReadyNative

namespace OAI.Algorithms

/-! Node readiness only inspects parked inputs and reusable node scratch.
The surrounding branch controller may independently update its own tapes. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram LeafHeadSetupProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- A sufficient set of frame cells for node readiness. The node index is a
separate collector field and is deliberately not inferred from this frame. -/
def ReadinessPort (i : Fin 768) : Prop :=
  i∈Node.cleanupPorts ∨ (730 ≤ i.val ∧ i.val < 744)

def branchControlPorts : List (Fin 768) := [320,322,323,324,330,331,332,333]

/-- This only proves disjointness from the readiness inputs. It makes no
claim that the node executable preserves every branch-control tape. -/
theorem readinessPort_not_branchControl (i : Fin 768) (hi : ReadinessPort i) :
    i∉branchControlPorts := by
  intro hm
  simp only [branchControlPorts,List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [ReadinessPort,Node.mem_cleanup] at hi

variable {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data} {hg : Guard (q.input k)}
  {W V L : ℕ} (p : Query.Preparation q k a hg W V L)

/-- Exact whole-frame equality is unnecessary: parked inputs and clean node
scratch suffice. Actual counter encoding and high-assignment semantics remain
separate obligations of the enclosing branch execution. -/
theorem query_collector_ready_relevant (hb : NodeNative.Blank a)
    (node : Fin (Query.packingProblem q k hg).Q)
    (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool)
    (rr : Fin 40 → Bool) (store : LeafNodeSamplesProgram.Store)
    (hf : ∀ i,ReadinessPort i → store.frame i=(branch p counter regs high).stacks i)
    (hn : store.index=unary node.val) (hs : store.shape=[]) :
    NodeNative.Ready (Native.queryInputsAddressed q k hg p.firstWord p.remainingWords node)
      (LeafNodeSamplesProgram.state rr store) := by
  apply collector_ready _ rr store _ _ hn hs
  · apply (branch_parked p node counter regs high).congr
    intro i hi hj
    exact hf i (Or.inr ⟨hi,hj⟩)
  · intro i hi hn'
    change store.frame i=[]
    rw [hf i (Or.inl hi)]
    exact branch_blank p hb counter regs high i hi hn'

/-- In particular, the eight branch-control cells may differ arbitrarily.
No equality for their bytes or for the arbitrary carried streams is assumed. -/
theorem query_collector_ready_off_branchControl (hb : NodeNative.Blank a)
    (node : Fin (Query.packingProblem q k hg).Q)
    (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool)
    (rr : Fin 40 → Bool) (store : LeafNodeSamplesProgram.Store)
    (hf : ∀ i,i∉branchControlPorts → store.frame i=(branch p counter regs high).stacks i)
    (hn : store.index=unary node.val) (hs : store.shape=[]) :
    NodeNative.Ready (Native.queryInputsAddressed q k hg p.firstWord p.remainingWords node)
      (LeafNodeSamplesProgram.state rr store) := by
  apply query_collector_ready_relevant p hb node counter regs high rr store _ hn hs
  intro i hi
  exact hf i (readinessPort_not_branchControl i hi)

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady

end

end OAI.Algorithms
