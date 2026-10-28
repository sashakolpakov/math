import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramValue
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramBounds

namespace OAI.Algorithms

/-! The exact finite-command node iteration, interpreted in its represented
ring. The local producer premise is an actual trace, discharged by the native
local-correction theorem in the model specialization. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram
open Polynomial
open CRTLocalProgram (ServiceSpec)

theorem iteration_run {C A : Type*} [CommRing A] {Q : ℕ}
    (encode : C → List Bool) (decode : C → A)
    (localCode multiply add : Cmd 16 256) (mulOp addOp : C → C → C)
    (Km Ka Kl W J : ℕ) (d : Data)
    (nodes : Fin Q → C) (remaining processed : List (Fin Q)) (i : Fin Q)
    (hfull : List.finRange Q = processed.reverse ++ i :: remaining)
    (unit minusOne zero acc : C)
    (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp Km)
    (ha : ServiceSpec (d.stacks ∘ localPorts) encode add addOp Ka)
    (hmd : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (had : ∀ a b, decode (addOp a b) = decode a + decode b)
    (hunit : decode unit = 1) (hminus : decode minusOne = -1) (hzero : decode zero = 0)
    (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
    (hr : d.stacks 257 = (remaining.map nodes).flatMap encode)
    (hp : d.stacks 258 = (processed.map nodes).flatMap encode)
    (hu : d.stacks 207 = encode unit) (hn : d.stacks 211 = encode minusOne)
    (hz : d.stacks 104 = encode zero) (hx : d.stacks 259 = encode (nodes i))
    (hacc : d.stacks 261 = encode acc) (hJ : d.stacks 243 = List.replicate J true)
    (h277 : (d.stacks 277).length = J * W)
    (hc : ∀ j ∈ cleanPorts, d.stacks j = [])
    (correction : List C) (hcl : correction.length = J) (H : A[X])
    (hdenote : PolynomialAlgorithm.denote (correction.map decode) = H)
    (hlocal : SubexpConvolutionControl.ExecutesIn localCode Kl
      ((Local.prepared d).stacks ∘ localPorts)
      (Function.update ((Local.prepared d).stacks ∘ localPorts) 244
        (HornerProgram.encodePolynomial encode correction))) :
    ∃ n ≤ budget Q J W Km Ka Kl, ∃ rf b,
      Eval (command localCode multiply add) n d
        ⟨rf, Function.update d.stacks 261 (encode b)⟩ ∧
      decode b = decode acc + (JetCRT.cofactor (decode ∘ nodes) J i).eval 0 *
        H.eval (-decode (nodes i)) := by
  obtain ⟨n, hn, rf, he⟩ := command_run encode localCode multiply add mulOp addOp
    Km Ka Kl W J d (remaining.map nodes) (processed.map nodes) correction
    unit minusOne zero (nodes i) acc hm ha hw hW hr hp hu hn hz hx hacc hJ hcl h277 hc hlocal
  refine ⟨n, ?_, rf, _, he, ?_⟩
  · apply hn.trans
    apply reconstructionProgramBudgetAux
  · exact indexed_nodeValue_decode decode mulOp addOp hmd had minusOne zero unit acc
      hminus hzero hunit nodes J remaining processed i hfull correction H hdenote
where
  reconstructionProgramBudgetAux :
      budget ((remaining.map nodes).length + (processed.map nodes).length) J W Km Ka Kl ≤
        budget Q J W Km Ka Kl := by
    apply middleBudget_mono _ le_rfl le_rfl le_rfl le_rfl le_rfl
    have hlen := congrArg List.length hfull
    simp only [List.length_finRange, List.length_append, List.length_reverse, List.length_cons] at hlen
    simp only [List.length_map]
    omega

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

end OAI.Algorithms
