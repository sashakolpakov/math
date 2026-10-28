import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyController

namespace OAI.Algorithms

/-! The fully instantiated packing controller is a single finite primitive bit
machine. Its bound includes generation, arithmetic, parsing and selection. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.SqrtLog.Packing

section Controller
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

omit [Fintype I] [Fintype E] [DecidableEq I] in
theorem controller_primitive (a : Word r Q) (tail : List (Word r Q))
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
    ∃ e : Data,
      SubexponentialSAT.Computation.RunsIn (primitive (SequentialProgram.program command)).step
        (primitiveOverhead (SequentialProgram.program command) *
          controllerCost a tail pairs vertices factors raw s M nb sb mb rb)
        (primitiveCfg (SequentialProgram.program command)
          (d.withPC (some (SequentialProgram.program command).entry)))
        (primitiveCfg (SequentialProgram.program command) (e.withPC none)) ∧
      e.stacks 8=((selectedValues ivar factor a tail
        (pairs.map Sum.inl++PackingHeadIncremental.headTerms (I:=I) (Q:=Q) vertices)
        (headsFirstIndices vertices factors) w).reverse.map ReadPlan.encodeWord).flatten := by
  obtain ⟨e,htrace,hout⟩ := controller_runsIn ivar factor a tail haN haC
    pairs vertices factors hvN hvC hindices raw s M nb sb mb rb hn hs hmass hr hraw w hwi hwh d hm hc he
  exact ⟨e,primitive_execution (SequentialProgram.program command) htrace,hout⟩

end Controller
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
