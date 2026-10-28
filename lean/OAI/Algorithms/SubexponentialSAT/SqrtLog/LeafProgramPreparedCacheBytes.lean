import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedSource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryArithmetic

namespace OAI.Algorithms

/-! The actual interpolation and denominator output tapes agree with the
source bank's typed fields. No independently supplied cache bytes are used. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
noncomputable section

variable (s : LeafHeadSetupProgram.Native.Inputs) (m : Circuit.Model)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height (LeafHeadSetupProgram.unary s.R) s.width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33)) (half : RingProgram.ScalarCode 3 (m.val 33))
    (e : LeafRingSetupProgram.Data) (base out : Factor.Data)
    (ho : Query.ArithmeticOutput base out m hd M cache half e) (hfield : s.Q < 3^(m.val 34))
    (hQ : m.val 21=s.Q) (hR : (base.stacks 740).length=s.R)

 theorem arithmetic_source_bytes (hQ : m.val 21=s.Q) (hR : (base.stacks 740).length=s.R) :
    let p := SourceBank.Parameters.ofProduced s words hc m ht hd M cache half e ho.produced hfield
    out.stacks 713=(List.ofFn (fun i=>RingProgram.flat (p.inverse i))).flatten ∧
    out.stacks 714=(List.ofFn (fun i=>RingProgram.flat (p.negative i))).flatten ∧
    out.stacks 715=(List.ofFn (fun i=>(List.ofFn (fun j=>RingProgram.flat (p.difference i j))).flatten)).flatten ∧
    out.stacks 716=p.rowWidth ∧ out.stacks 717=p.ringWidth ∧
    out.stacks 728=RingProgram.flat p.invDenom := by
  dsimp only
  let p := SourceBank.Parameters.ofProduced s words hc m ht hd M cache half e ho.produced hfield
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [ho.inverse,hQ]
    exact SourceBank.Parameters.inverseBytes_eq p
  · rw [ho.negative,hQ]
    exact SourceBank.Parameters.negativeBytes_eq p
  · rw [ho.difference,hQ]
    exact SourceBank.Parameters.differenceBytes_eq p
  · rw [ho.nodesLength,hQ]
    rfl
  · rw [ho.width]
    rfl
  · rw [ho.denominator,hR]
    rfl

 theorem arithmetic_source_constants :
    let p := SourceBank.Parameters.ofProduced s words hc m ht hd M cache half e ho.produced hfield
    out.stacks 280=RingProgram.flat p.ops.zeroRun.1 ∧
    out.stacks 207=RingProgram.flat p.ops.oneRun.1 ∧
    out.stacks 211=RingProgram.flat p.minusOne := by
  refine ⟨?_,?_,?_⟩
  · exact (ho.low 280 (by decide)).trans ho.produced.caches.fullZero_model
  · exact (ho.low 207 (by decide)).trans ho.produced.caches.fullOne_model
  · exact (ho.low 211 (by decide)).trans (ho.produced.caches.fullMinusOne.trans (LeafProgram.Constants.constantCode_flat _ _ _).symm)

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
