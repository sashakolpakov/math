import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyNode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedCacheBytes
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedPersistent

namespace OAI.Algorithms

/-! The physical source constants at a node follow from the executed query
arithmetic and the proved persistent-port frame. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram PreparedSource
noncomputable section

 theorem sourceStatic_of_arithmetic
    (s : LeafHeadSetupProgram.Native.Inputs) (m : Circuit.Model)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height (LeafHeadSetupProgram.unary s.R) s.width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33)) (half : RingProgram.ScalarCode 3 (m.val 33))
    (e : LeafRingSetupProgram.Data) (base out node : Factor.Data)
    (ho : Query.ArithmeticOutput base out m hd M cache half e)
    (hfield : s.Q < 3^(m.val 34)) (hQ : m.val 21=s.Q) (hR : (base.stacks 740).length=s.R)
    (hp : Persistent out node) :
    SourceStatic (SourceBank.Parameters.ofProduced s words hc m ht hd M cache half e ho.produced hfield) node := by
  obtain ⟨hi,hn,hdiff,hr,hw,hinv⟩ :=
    arithmetic_source_bytes s m ht hd words hc M cache half e base out ho hfield hQ hR
  obtain ⟨hz,hone,hm⟩ := arithmetic_source_constants s m ht hd words hc M cache half e base out ho hfield
  exact ⟨(hp 713 (by simp [persistentPorts])).trans hi,
    (hp 714 (by simp [persistentPorts])).trans hn,
    (hp 715 (by simp [persistentPorts])).trans hdiff,
    (hp 717 (by simp [persistentPorts])).trans hw,
    (hp 716 (by simp [persistentPorts])).trans hr,
    (hp 280 (by simp [persistentPorts])).trans hz,
    (hp 207 (by simp [persistentPorts])).trans hone,
    (hp 211 (by simp [persistentPorts])).trans hm,
    (hp 728 (by simp [persistentPorts])).trans hinv⟩

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
