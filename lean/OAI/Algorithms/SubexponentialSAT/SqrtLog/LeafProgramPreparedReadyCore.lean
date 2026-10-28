import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyPreparation

namespace OAI.Algorithms

/-! The arithmetic core and scalar zero are consequences of the actual
node initializer, for the same factor specification used by the callback. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open NodeNative LeafHeadSetupProgram MomentsProgram MomentsAssembly

 theorem preparation_factor_core {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : Ready s a) {d : ℕ}
    (q : Factor.Spec s.r s.Q s.n d) (hf : FactorStatic q a)
    (hprecision : a.stacks 212=List.replicate q.u true) :
    ∀ i : Fin 56,b.stacks (corePorts i)=
      Product.tapes (emptyCore (FactorLoop.assignmentEnvironment q (List.replicate d true))) i := by
  exact pr.core_words ha 3 q.p.t q.p.modulus q.p.cache q.ctx.table
    (List.replicate d true) q.width q.u q.J hf.modulus hf.table hf.width
    hf.scalarZero hf.degree hprecision hf.target

 theorem preparation_factor_zero {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : Ready s a) {d : ℕ}
    (q : Factor.Spec s.r s.Q s.n d) (hf : FactorStatic q a) :
    b.stacks 190=RingProgram.flat q.p.ops.zeroRun.1 :=
  pr.zero_word ha q.p.ops.zeroRun.1 hf.source.zero

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
