import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedSpec
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgramModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputPackingTransport

namespace OAI.Algorithms

/-! The factor specification uses the actual generated idempotent code and
native node word. The existential scalar preparation of the code is retained
as a witness; no canonical-byte assumption is needed. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
noncomputable section

structure GeneratedCode (t : ℕ) (bits : List Bool) where
  modulus : SubexpPreparedQuartic.Modulus 3 t
  cache : RingProgram.ScalarCache 3 t
  half : RingProgram.ScalarCode 3 t
  bytes : bits=RingProgram.flat (IdempotentProgram.binaryLiftWords t modulus cache half)
  inverse : (2 : ZMod (3^t))*wordValue 3 t half=1

def GeneratedCode.code {t : ℕ} {bits : List Bool} (g : GeneratedCode t bits) :=
  IdempotentProgram.binaryLiftWords t g.modulus g.cache g.half

def generatedCode {m : LeafParametersProgram.Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)}
    {half : RingProgram.ScalarCode 3 (m.val 33)} {e : LeafRingSetupProgram.Data}
    (hp : LeafRingSetupProgram.Produced m hd M cache half e) :
    GeneratedCode (m.val 33) (e.stacks 281) :=
  let h := hp.idempotent
  ⟨h.choose,h.choose_spec.choose,h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.1,h.choose_spec.choose_spec.choose_spec.2⟩

def nativeSpecOfInputs (s : LeafHeadSetupProgram.Native.Inputs)
    (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height (LeafHeadSetupProgram.unary s.R) s.width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33)) (half : RingProgram.ScalarCode 3 (m.val 33))
    (e : LeafRingSetupProgram.Data) (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : s.Q < 3^(m.val 34)) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (J : ℕ) (hJ : 0 < J) (source : List (List (SAT.Literal (Fin s.n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source) :
    Factor.Spec s.r s.Q s.n (m.val 34) :=
  factorSpec (SourceBank.Parameters.ofProduced s words hc m ht hd M cache half e hp hfield)
    s.plans (PackingIncidenceInput.reindexPacking s.plans_length.symm s.packing)
    q hv J hJ source hsource (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (s.node.val+1))
    (e.stacks 202) hp.caches.width (generatedCode hp).code

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
