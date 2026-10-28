import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteQueryMeaning
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeAddressedQuery

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete
open SubexponentialSAT.MulticolorTypes PackingCallerProgram LeafProgram.NodeConcrete
open PackingIncidenceInput BucketProgram
open LeafHeadSetupProgram

variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
variable (a : Word ((LeafProgram.Query.packingProblem q k hg)).r ((LeafProgram.Query.packingProblem q k hg)).Q) (tail : List (Word ((LeafProgram.Query.packingProblem q k hg)).r ((LeafProgram.Query.packingProblem q k hg)).Q)) (t : Fin ((LeafProgram.Query.packingProblem q k hg)).Q)

def NativeQueryMeaning (tables : List HeadTable) (hlen : tables.length=((Native.queryInputsAddressed q k hg a tail t)).r) : Prop :=
  FinalizedMeaning (planHigh (LeafProgram.Query.packingProblem q k hg)) (queryFreeHead (LeafProgram.Query.packingProblem q k hg) a tail t)
    (addressedEntries ((LeafProgram.Query.packingProblem q k hg)).scopes ((LeafProgram.Query.packingProblem q k hg)).n ((LeafProgram.Query.packingProblem q k hg)).mask).length
    (queryMatrix (LeafProgram.Query.packingProblem q k hg) a tail ((Native.queryInputsAddressed q k hg a tail t)).height.length ((Native.queryInputsAddressed q k hg a tail t)).R t) tables hlen ∧
  (∀ g : Fin ((LeafProgram.Query.packingProblem q k hg)).r,(tables.get (Fin.cast hlen.symm g)).mask=
    List.ofFn (headMask (planHigh (LeafProgram.Query.packingProblem q k hg)) (queryFreeHead (LeafProgram.Query.packingProblem q k hg) a tail t) g)) ∧
  (∀ g : Fin ((LeafProgram.Query.packingProblem q k hg)).r,LeafStatisticsProgram.Arity.decoded
    (tables.get (Fin.cast hlen.symm g)).context=
    (List.range ((LeafProgram.Query.packingProblem q k hg)).factors).filter (fun f=>decide (planColor (LeafProgram.Query.packingProblem q k hg) a tail t f=g)))

theorem native_query_meaning {base : LeafHeadSetupProgram.Data} {tables : List HeadTable}
    (hp : ProducedHeads base ((Native.queryInputsAddressed q k hg a tail t)).n ((Native.queryInputsAddressed q k hg a tail t)).N ((Native.queryInputsAddressed q k hg a tail t)).D ((Native.queryInputsAddressed q k hg a tail t)).rows ((Native.queryInputsAddressed q k hg a tail t)).low ((Native.queryInputsAddressed q k hg a tail t)).relation ((Native.queryInputsAddressed q k hg a tail t)).columnLength
      (((Native.queryInputsAddressed q k hg a tail t)).node.val*((Native.queryInputsAddressed q k hg a tail t)).r) tables)
    (hlen : tables.length=((Native.queryInputsAddressed q k hg a tail t)).r)
    (hW : ((Native.queryInputsAddressed q k hg a tail t)).offset ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141)) :
    NativeQueryMeaning q k hg a tail t tables hlen := by
  have hmask : ((LeafProgram.Query.packingProblem q k hg)).mask.length=((LeafProgram.Query.packingProblem q k hg)).n := by
    simp [LeafProgram.Query.packingProblem,LeafQueryFrontend.Query.forward,
      LeafQueryFrontend.highMask]
  have hp' : ProducedHeads base ((LeafProgram.Query.packingProblem q k hg)).n ((LeafProgram.Query.packingProblem q k hg)).factors
      (addressedEntries ((LeafProgram.Query.packingProblem q k hg)).scopes ((LeafProgram.Query.packingProblem q k hg)).n ((LeafProgram.Query.packingProblem q k hg)).mask).length (ProducedQueryRank.rows (LeafProgram.Query.packingProblem q k hg) a tail)
      (((LeafProgram.Query.packingProblem q k hg)).mask.map Bool.not)
      (ProducedRank.FiberRel (addressedEntries ((LeafProgram.Query.packingProblem q k hg)).scopes ((LeafProgram.Query.packingProblem q k hg)).n ((LeafProgram.Query.packingProblem q k hg)).mask)
        (ProducedRank.entryNat (ProducedQueryRank.packing (LeafProgram.Query.packingProblem q k hg) a tail) ((Native.queryInputsAddressed q k hg a tail t)).height.length ((Native.queryInputsAddressed q k hg a tail t)).R t)
        ((Native.queryInputsAddressed q k hg a tail t)).offset) ((Native.queryInputsAddressed q k hg a tail t)).columnLength (t.val*((LeafProgram.Query.packingProblem q k hg)).r) tables := by
    simpa only [Native.queryInputsAddressed,Native.queryInputs,Native.Inputs.relation,
      LeafProgram.Query.packingProblem,PackingCallerProgram.Problem.incidences,
      addressedEntries_length] using hp
  exact ⟨query_finalized (LeafProgram.Query.packingProblem q k hg) a tail ((Native.queryInputsAddressed q k hg a tail t)).height.length ((Native.queryInputsAddressed q k hg a tail t)).R t hmask hp' hlen hW,
    query_masks (LeafProgram.Query.packingProblem q k hg) a tail t hmask hp' hlen,query_contexts (LeafProgram.Query.packingProblem q k hg) a tail t hp' hlen⟩

theorem native_query_started (d : LeafHeadSetupProgram.Data) (hd : Native.Ready (Native.queryInputsAddressed q k hg a tail t) d)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    {tables : List HeadTable}
    (hp : ProducedHeads (Native.start (Native.queryInputsAddressed q k hg a tail t) d ra rd rc words) ((Native.queryInputsAddressed q k hg a tail t)).n ((Native.queryInputsAddressed q k hg a tail t)).N ((Native.queryInputsAddressed q k hg a tail t)).D ((Native.queryInputsAddressed q k hg a tail t)).rows ((Native.queryInputsAddressed q k hg a tail t)).low
      ((Native.queryInputsAddressed q k hg a tail t)).relation ((Native.queryInputsAddressed q k hg a tail t)).columnLength (((Native.queryInputsAddressed q k hg a tail t)).node.val*((Native.queryInputsAddressed q k hg a tail t)).r) tables)
    (hlen : tables.length=((Native.queryInputsAddressed q k hg a tail t)).r) : NativeQueryMeaning q k hg a tail t tables hlen := by
  apply native_query_meaning q k hg a tail t hp hlen
  rw [Native.start_low (Native.queryInputsAddressed q k hg a tail t) d ra rd rc words 141 (by decide),hd.offset]

end SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

end

end OAI.Algorithms
