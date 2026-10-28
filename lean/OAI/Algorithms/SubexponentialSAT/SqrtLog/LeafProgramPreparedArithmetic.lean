import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedArithmeticBase

namespace OAI.Algorithms
/-! The shared arithmetic context of the node and reconstruction programs is
formed from the actual ring producer, using its literal width and degree words. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
noncomputable section

variable (q : LeafQueryFrontend.Query) (k : ℕ) (l : Fin 8 → ℕ) (hg : Guard (q.input k))
    (M : SubexpPreparedQuartic.Modulus 3 ((numeric q k l).val 33))
    (cache : RingProgram.ScalarCache 3 ((numeric q k l).val 33))
    (half : RingProgram.ScalarCode 3 ((numeric q k l).val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced (numeric q k l) (Query.ring_degree_pos (q.input k) l hg)
      M cache half e)

def nodeArithmetic : Residual.Native.NodeArithmetic :=
  nodeArithmeticOfProduced (numeric q k l) (Query.ring_precision_pos (q.input k) l hg)
    (Query.ring_degree_pos (q.input k) l hg) (produce (q.input k)).J (produce_J_pos (q.input k))
    M cache half e hp

theorem nodeArithmetic_words :
    e.stacks 194=(nodeArithmetic q k l hg M cache half e hp).modulus.bits ∧
    e.stacks 201=RingTriple.tableEncoding (nodeArithmetic q k l hg M cache half e hp).table ∧
    e.stacks 202=(nodeArithmetic q k l hg M cache half e hp).width ∧
    e.stacks 203=(nodeArithmetic q k l hg M cache half e hp).cache.zero.val ∧
    e.stacks 204=(nodeArithmetic q k l hg M cache half e hp).degree ∧
    e.stacks 212=List.replicate (nodeArithmetic q k l hg M cache half e hp).u true ∧
    e.stacks 243=List.replicate (nodeArithmetic q k l hg M cache half e hp).J true ∧
    e.stacks 207=RingProgram.flat (nodeArithmetic q k l hg M cache half e hp).one ∧
    e.stacks 280=RingProgram.flat (nodeArithmetic q k l hg M cache half e hp).zero :=
  nodeArithmeticOfProduced_words (numeric q k l) (Query.ring_precision_pos (q.input k) l hg)
    (Query.ring_degree_pos (q.input k) l hg) (produce (q.input k)).J (produce_J_pos (q.input k))
    M cache half e hp (numeric_J q k l hg)

theorem nodeInput_of_frame (s : NodeNative.HeadInputs) (a : Factor.Data)
    (hr : NodeNative.Ready s a)
    (hf : ∀ i : Fin 640,i∈([194,201,202,203,204,207,212,243,280] : List (Fin 640)) →
      a.stacks (LeafRingSetupProgram.wideStacks i)=e.stacks i)
    (ho : a.stacks 102=[]) :
    Residual.Native.NodeInput (nodeArithmetic q k l hg M cache half e hp) s a := by
  obtain ⟨h194,h201,h202,h203,h204,h212,h243,h207,h280⟩ :=
    nodeArithmetic_words q k l hg M cache half e hp
  exact ⟨hr,(hf 194 (by simp)).trans h194,(hf 201 (by simp)).trans h201,
    (hf 202 (by simp)).trans h202,(hf 203 (by simp)).trans h203,
    (hf 204 (by simp)).trans h204,(hf 212 (by simp)).trans h212,
    (hf 243 (by simp)).trans h243,(hf 207 (by simp)).trans h207,
    (hf 280 (by simp)).trans h280,ho⟩

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
