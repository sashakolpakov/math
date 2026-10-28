import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeLocal

namespace OAI.Algorithms

/-! Erase only opaque collector accumulators for the node's proof run.
The concrete node footprint theorem replays that run on the original state. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native
open SubexponentialSAT BitProgram StructuredCalls LeafNodeSamplesProgram MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

 def maskStore (s : Store) : Store :=
  {s with source:=[],payload:=[],nodesRev:=[],jetsRev:=[],temporary:=[],nodesOut:=[],jetsOut:=[]}

 theorem maskStore_tapes (s : Store) (i : Fin 768) :
    tapes (maskStore s) i=if i∈NodeNative.carriedPorts then [] else tapes s i := by
  by_cases hi : i∈NodeNative.carriedPorts
  · simp only [NodeNative.carriedPorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [maskStore,tapes,NodeNative.carriedPorts]
  · have hn := hi
    simp only [NodeNative.carriedPorts,List.mem_cons,List.mem_nil_iff,or_false,not_or] at hn
    simp only [maskStore,tapes,ite_eq_right hi,ite_eq_right hn.1,ite_eq_right hn.2.1,
      ite_eq_right hn.2.2.1,ite_eq_right hn.2.2.2.1,ite_eq_right hn.2.2.2.2.1,
      ite_eq_right hn.2.2.2.2.2.1,ite_eq_right hn.2.2.2.2.2.2]

 theorem maskStore_wordBound (s : Store) (regs : Fin 40 → Bool) (B : ℕ)
    (hb : NodeNative.LocalWordBound B (state regs s)) :
    SubexponentialSAT.SubexpSetupStorage.WordBound B (state regs (maskStore s)) := by
  intro i
  change (tapes (maskStore s) i).length ≤ B
  rw [maskStore_tapes]
  by_cases hi : i∈NodeNative.carriedPorts
  · simp [hi]
  · rw [ite_eq_right hi]
    change ((state regs s).stacks i).length ≤ B
    exact hb i hi

 theorem maskStore_good {c : NodeArithmetic} {s : NodeNative.HeadInputs}
    {relation : AssignmentContext → List Bool → Contribution s.n (SubexpLiftRing.baseWidth 3 c.t) c.d → Prop}
    (w : NodeWitness c s relation)
    (Valid : (Fin 768 → List Bool) → Prop) (nodes : ℕ → List Bool) (i : ℕ) :
    Valid (maskStore w.store).frame ∧ (maskStore w.store).index=List.replicate i true ∧
      (maskStore w.store).node=nodes i ∧ (maskStore w.store).jet=[] ∧ (maskStore w.store).shape=[]
      ↔ w.good Valid nodes i := Iff.rfl

end SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native

end OAI.Algorithms
