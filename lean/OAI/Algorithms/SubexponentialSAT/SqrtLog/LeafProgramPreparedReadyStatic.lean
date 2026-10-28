import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyCache
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyQueryFields

namespace OAI.Algorithms

/-! Assembly of the static factor fields from the executed arithmetic,
query source tapes and persistent-port frame. The two node-specific words
are the actual node and the chosen high-variable assignment. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram PreparedSource
noncomputable section

 theorem native_static_of_arithmetic
    (s : LeafHeadSetupProgram.Native.Inputs) (m : Circuit.Model)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height (LeafHeadSetupProgram.unary s.R) s.width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33)) (half : RingProgram.ScalarCode 3 (m.val 33))
    (e : LeafRingSetupProgram.Data) (base out node : Factor.Data)
    (ho : Query.ArithmeticOutput base out m hd M cache half e)
    (hfield : s.Q < 3^(m.val 34)) (hQ : m.val 21=s.Q) (hR : (base.stacks 740).length=s.R)
    (hp : Persistent out node) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (J : ℕ) (hJ : 0 < J) (hmJ : m.val 42=J)
    (source : List (List (SAT.Literal (Fin s.n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (hf : QueryFields q node) (hindex : q.index=Encoding.encodeNat (markIndex q))
    (hdegree : e.stacks 204=List.replicate (m.val 34) true)
    (htheta : node.stacks 78=RingProgram.flat
      (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (s.node.val+1)))
    (hhigh : (node.stacks 703).length=s.n) :
    FactorStatic (nativeSpecOfInputs s m ht hd words hc M cache half e ho.produced
      hfield q hv J hJ source hsource) node := by
  have low (i : Fin 640) (hi : i∈([194,201,202,203,204,243,281] : List (Fin 640))) :
      node.stacks (LeafRingSetupProgram.wideStacks i)=e.stacks i := by
    have hmem : LeafRingSetupProgram.wideStacks i∈persistentPorts := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have hlt : i.val < 340 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact (hp _ hmem).trans (ho.low i hlt)
  refine ⟨sourceStatic_of_arithmetic s m ht hd words hc M cache half e base out node
      ho hfield hQ hR hp,?_,?_,?_,?_,?_,htheta,?_,hhigh,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (low 194 (by simp)).trans ho.produced.caches.modulus
  · exact low 202 (by simp)
  · exact (low 203 (by simp)).trans ho.produced.caches.scalarZero
  · exact (low 201 (by simp)).trans ho.produced.native.table
  · exact (low 204 (by simp)).trans hdegree
  · have hwide : LeafRingSetupProgram.wideStacks (243 : Fin 640)=(243 : Fin 768) :=
      Fin.ext (by rfl)
    rw [(nativeSpecOfInputs_parameters s m ht hd words hc M cache half e
      ho.produced hfield q hv J hJ source hsource).2.1]
    simpa only [hwide,hmJ] using (low 243 (by simp)).trans ho.produced.jetOrder
  · exact hf.rows.trans (nativeSpecOfInputs_rows s m ht hd words hc M cache half e
      ho.produced hfield q hv J hJ source hsource).symm
  · change node.stacks 700=Encoding.encodeList id (HashInputProgram.Expansion.encodedClauses source)
    exact hf.clauses.trans (congrArg (Encoding.encodeList id) hsource)
  · change node.stacks 704=List.replicate
      (((castRows (congrArg List.length hsource) q.rows).map
        (fun ts=>(HashInputProgram.Loop.rawInput q.width.length ts).reverse)).length) true
    simpa only [List.length_map,castRows_length] using hf.count
  · exact hf.index.trans hindex
  · exact hf.marked
  · exact congrArg List.length hf.width
  · change BinaryArithmetic.toNat (node.stacks 707)=
      (HashInputProgram.Expansion.encodedClauses source).length
    rw [hf.modulus,←hsource]
    exact hv.2.2.2.2.2.1
  · exact (low 281 (by simp)).trans (nativeSpecOfInputs_code s m ht hd words hc M cache half e
      ho.produced hfield q hv J hJ source hsource)

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
