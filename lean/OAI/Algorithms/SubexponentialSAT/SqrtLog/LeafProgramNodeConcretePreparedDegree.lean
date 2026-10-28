import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcretePreparedBudget
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFactorFields
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteQueryBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryWidthPacking

namespace OAI.Algorithms

/-! The actual guarded parameter producer pays for the degree of the same
source target used by the native readout theorem. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open SubexponentialSAT MulticolorTypes SubexpLiftRing SubexpQuarticRing LeafParametersProgram

 theorem query_prepared_degree
    (q : LeafQueryFrontend.Query) (hv : q.Valid) (k : ℕ) (hg : Guard (q.input k))
    (first : MulticolorTypes.Word (Query.packingProblem q k hg).r (Query.packingProblem q k hg).Q)
    (tail : List (MulticolorTypes.Word (Query.packingProblem q k hg).r (Query.packingProblem q k hg).Q)) (node : Fin (Query.packingProblem q k hg).Q)
    (lengths : Fin 8 → ℕ) (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node).height (LeafHeadSetupProgram.unary (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node).R) (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node).width words)
    (M : SubexpPreparedQuartic.Modulus 3 ((PreparedSource.numeric q k lengths).val 33))
    (cache : RingProgram.ScalarCache 3 ((PreparedSource.numeric q k lengths).val 33))
    (half : RingProgram.ScalarCode 3 ((PreparedSource.numeric q k lengths).val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced (PreparedSource.numeric q k lengths) (Query.ring_degree_pos (q.input k) lengths hg) M cache half e)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (hwidth : ∀ clause∈source,clause.length ≤ k)
    (H : Finset (Fin (Query.packingProblem q k hg).n)) (high : H → Bool) :
    (specTarget (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) (PreparedSource.numeric q k lengths) (Query.ring_precision_pos (q.input k) lengths hg) (Query.ring_degree_pos (q.input k) lengths hg) words hc M cache half e hp (PreparedSource.numeric_field q k lengths hg) q hv ((produce (q.input k)).J) (produce_J_pos (q.input k)) source hs) H high).natDegree < (Query.packingProblem q k hg).Q*(produce (q.input k)).J := by
  apply nativeSpec_degree_of_budget (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) (PreparedSource.numeric q k lengths) (Query.ring_precision_pos (q.input k) lengths hg) (Query.ring_degree_pos (q.input k) lengths hg) words hc M cache half e hp (PreparedSource.numeric_field q k lengths hg) q hv ((produce (q.input k)).J) (produce_J_pos (q.input k)) source hs H high k (q.input k).factors hwidth
  · have h := BucketTupleProgram.Concrete.query_rows_le_factors q k hg
    rw [Query.Width.packing_factors_eq] at h
    exact h
  · rw [PreparedSource.numeric_t q k lengths hg]
    exact guard_hermite (q.input k) hg

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
