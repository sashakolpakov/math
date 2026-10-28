import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeContext

namespace OAI.Algorithms

/-! Uniform marked collector queries from the actual staged trial. Each
reference obtains its own concrete arithmetic/layout/branch preparation. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls LeafProgram LeafParametersProgram
open ProducedQueryResources
noncomputable section

 theorem massQueries_of_contexts (k B qi : ℕ) (a : LeafOuterProgram.Data)
    (ha : LeafOuterProgram.WorkerEmpty a) (query : List Bool → LeafQueryFrontend.Query)
    (count : List Bool → ℕ) (valid : List Bool → Prop)
    (words : ∀ bits, valid bits → OuterQuery.TrialWords (query bits) a)
    (hvalid : ∀ bits, valid bits → (query bits).Valid)
    (hmarked : ∀ bits, valid bits → (query bits).mark.isSome=true)
    (href : ∀ bits, valid bits → (query bits).index=bits)
    (hlarge : ∀ bits, valid bits → 2 ≤ ambient (query bits))
    (facts : ∀ bits, valid bits → RuntimeFacts (query bits) k B qi (markedCoefficient k) (markedExponent k))
    (contexts : ∀ bits (hv : valid bits) (base : Query.Data),
      MarkedInputFacts (query bits) base →
      ∀ V L (p : Query.Preparation (query bits) k
        (Query.markedInput (Query.Carried.reference base)) (facts bits hv).guard
        (Query.Carried.markedWidth base) V L),
      V=Query.modelValueCap (Circuit.result Serialization.code
        (Execute.guardedModel ((query bits).input k) p.lengths)) →
      L=Query.modelLengthCap (Circuit.result Serialization.code
        (Execute.guardedModel ((query bits).input k) p.lengths)) →
      Nonempty (PreparedCountContext p base (count bits) B qi)) :
    LeafOuterNative.MassQueries k a count
      (fun bits => queryLimit k qi (markedCoefficient k) (markedExponent k) (query bits))
      (fun bits => queryLimit k qi (markedCoefficient k) (markedExponent k) (query bits)+1)
      valid := by
  intro loaded hloaded
  apply markedKernel k
  intro bits tail base hv hb
  let start := markedStart base tail bits
  have inputs : MarkedInputFacts (query bits) start :=
    marked_input_from_trial a ha (words bits hv) (hmarked bits hv) bits (href bits hv)
      loaded _ hloaded base tail hb
  obtain ⟨V,L,p,hV,hL⟩ := Query.Carried.marked_construct (query bits) k start
    (hvalid bits hv) (facts bits hv).guard inputs.clean inputs.sources inputs.marked
    inputs.reference inputs.zero inputs.high
  obtain ⟨ctx⟩ := contexts bits hv start inputs V L p hV hL
  refine ⟨ctx.width,?_⟩
  exact polynomialMarked_of_context start (facts bits hv) p ctx.execution
    (hvalid bits hv) inputs.clean inputs.sources inputs.marked inputs.reference inputs.zero inputs.high
    (hlarge bits hv) hV hL ctx.step ctx.stepWidth ctx.referenceBound

end
end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
