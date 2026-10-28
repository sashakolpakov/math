import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeContract

namespace OAI.Algorithms

/-! Closed correctness of the actual per-node head setup. Every machine in
this theorem is fixed code; hypotheses describe the supplied runtime input. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open BucketTupleProgram (enumerate)

theorem command_eval (s : Inputs) (a : LeafHeadSetupProgram.Data) (ha : Ready s a) :
    ∃ ra rd rc words tables costs steps e,
      CacheCorrect s.height (unary s.R) s.width words ∧
      ProducedHeads (start s a ra rd rc words) s.n s.N s.D s.rows s.low
        s.relation s.columnLength (s.node.val*s.r) tables ∧
      tables.length=s.r ∧ costs.length=s.r ∧ Eval command steps a e ∧
      e.stacks 163=MomentsAssembly.bucketsInput
        (((enumerate tables).map (BucketTupleProgram.Representative.bucket s.n)).reverse) ∧
      (∀ i,External i→e.stacks i=a.stacks i) ∧
      (∀ i : Fin 768,640 ≤ i.val ∧ i.val < 680→e.stacks i=[]) ∧
      (∀ i : Fin 288,e.stacks (workPort (by decide) i)=[]) ∧
      e.stacks 710=words.flatten++a.stacks 710 ∧
      e.stacks 711=List.replicate (s.R*s.width.length) false++a.stacks 711 ∧
      e.stacks 712=s.power.1++a.stacks 712 ∧
      (∃ loopEnd rf,
        CostTrace entry (start s a ra rd rc words) s.n s.N s.D (s.Q*s.r) s.rows s.low
          s.relation s.columnTime s.columnLength (s.node.val*s.r) [[]] tables costs
          (start s a ra rd rc words) loopEnd ∧
        e=clearManyState cleanupPorts (finalResult loopEnd rf (unary s.n) (enumerate tables)) ∧
        steps ≤ nodeCost a ra rd rc s.n s.r s.node.val s.records s.height (unary s.R)
          s.width words tables costs loopEnd rf ∧
        loopEnd.stacks 660=BucketTupleProgram.Representative.tuplesBits (enumerate tables) ∧
        loopEnd.stacks 128=unary s.n) := by
  have hc := node_contract s a ha
  have hv : ∀ z j,j < s.records.length→∀ v∈selectedHeads s.n s.rows s.low z,s.valid j v := by
    intro z j hj v hv
    refine ⟨?_,?_⟩
    · simpa using hj
    · exact HeadIdentifierProgram.chosenIds_bound _ _ v hv
  have he := LeafHeadSetupProgram.command_eval entry a s.n s.N (s.Q*s.r) s.r s.node.val
    s.records s.rows s.low s.height (unary s.R) s.width ha.ambient ha.factors ha.colors
    ha.node ha.wordWidth ha.words ha.low (ha.plans.trans s.records_bytes.symm)
    ha.height ha.order ha.width s.rows_width s.rows_length
    (by simpa [unary] using s.width_boot) ha.tuples ha.marker s.valid s.relation
    s.columnTime s.columnLength hc hv
  simpa only [start,command,Inputs.records_length,Inputs.power,unary,List.length_replicate] using he

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
