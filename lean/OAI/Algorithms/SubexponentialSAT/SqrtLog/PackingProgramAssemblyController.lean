import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyRefinement
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyOrder
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramOrdering

namespace OAI.Algorithms

/-! The fully instantiated fixed controller computes the original greedy
packing labels using the native reduced-score producer. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.SqrtLog.Packing

section Controller
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

def controllerCost (a : Word r Q) (tail : List (Word r Q)) (pairs : List (I × I))
    (vertices : List V) (factors : List E) (raw : List PairScoreProgram.PlanPair)
    (s M : ℕ) (nb sb mb rb : List Bool) : ℕ :=
  let indices := headsFirstIndices vertices factors
  let cost := uniformBudget indices.length pairs.length raw.length (a::tail).length
    (ReadPlan.wordWidth r Q) vertices.length (magnitude vertices.length s M r) (parameterBits nb sb mb rb)
  indices.length*(cost+SequentialProgram.selectionBudget (a::tail).length
    (scoreBound (a::tail) pairs indices vertices.length s M) indices.length
    (ReadPlan.encodeWord a).length+3)+3

omit [Fintype I] [Fintype E] [DecidableEq I] in
theorem controller_runsIn (a : Word r Q) (tail : List (Word r Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail)
    (pairs : List (I × I)) (vertices : List V) (factors : List E)
    (hvN : vertices.Nodup) (hvC : ∀ v,v∈vertices)
    (hindices : ∀ x,x∈headsFirstIndices vertices factors)
    (raw : List PairScoreProgram.PlanPair) (s M : ℕ)
    (nb sb mb rb : List Bool)
    (hn : SubexponentialSAT.BinaryArithmetic.toNat nb=vertices.length) (hs : SubexponentialSAT.BinaryArithmetic.toNat sb=s)
    (hmass : SubexponentialSAT.BinaryArithmetic.toNat mb=M) (hr : SubexponentialSAT.BinaryArithmetic.toNat rb=r)
    (hraw : raw.Perm (pairs.map (PackingIncidenceProgram.incidencePair ivar factor
      (headsFirstIndices vertices factors))))
    (w : Weights)
    (hwi : w.incidence=vertices.length^2*(s*(a::tail).length^2)^2)
    (hwh : w.head=M^2*(2*r)^2)
    (d : Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail
      (headsFirstIndices vertices factors).length [] d.stacks)
    (hc : (d.stacks 11).length=(headsFirstIndices vertices factors).length)
    (he : SequentialProgram.HighState
      (environment (ScoreBuilderRawInput.environment 1 (a::tail)
        (headsFirstIndices vertices factors).length raw) nb sb mb rb) d.stacks) :
    ∃ e : Data, RunsIn (SequentialProgram.program command)
      (controllerCost a tail pairs vertices factors raw s M nb sb mb rb)
      (d.withPC (some (SequentialProgram.program command).entry)) (e.withPC none) ∧
      e.stacks 8=((selectedValues ivar factor a tail
        (pairs.map Sum.inl++PackingHeadIncremental.headTerms (I:=I) (Q:=Q) vertices)
        (headsFirstIndices vertices factors) w).reverse.map ReadPlan.encodeWord).flatten := by
  apply controller_runsIn_ordered ivar factor a tail
    (pairs.map Sum.inl++PackingHeadIncremental.headTerms (I:=I) (Q:=Q) vertices)
    (headsFirstIndices vertices factors) w
    (evaluate ivar factor (a::tail) pairs (headsFirstIndices vertices factors) a vertices.length s M)
    (scoreBound (a::tail) pairs (headsFirstIndices vertices factors) vertices.length s M)
  · intro remaining fixed hsize x y
    exact candidateScore_order ivar factor (a::tail) haN haC (by simp)
      pairs vertices factors hvN hvC w s M hwi hwh a remaining fixed hsize x y
  · intro remaining fixed x hsize _
    exact evaluate_bound ivar factor (a::tail) pairs (headsFirstIndices vertices factors)
      a vertices.length s M remaining fixed x hsize
  · exact refines ivar factor a tail pairs (headsFirstIndices vertices factors) hindices
      vertices.length s M raw nb sb mb rb hn hs hmass hr hraw
  · exact hm
  · exact hc
  · exact he

end Controller
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
