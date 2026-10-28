import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeQueryInventory
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopePolynomial
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorResourceProduced

namespace OAI.Algorithms

/-! Uniform storage for the actual query. Incoming physical input width is
kept separate from the assembled-work powers paying the large inventories. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.NodeEnvelope
open SubexponentialSAT BitProgram StructuredCalls MulticolorTypes SubexpLiftRing SubexpSetupStorage
open LeafProgram LeafProgram.NodeNative LeafHeadSetupProgram ProducedQueryResources
open LeafParametersProgram

variable (query : LeafQueryFrontend.Query) (k occurrence qi : ℕ)
  (hg : Guard (query.input k))
  (first : Word (problem query k hg).r (problem query k hg).Q)
  (tail : List (Word (problem query k hg).r (problem query k hg).Q))
  (node : Fin (problem query k hg).Q)

def queryStorageCap (input : ℕ) : ℕ :=
  let s := Native.queryInputsAddressed query k hg first tail node
  let p := resources query k occurrence qi hg first tail
  let v := produce (query.input k)
  assignmentCap s input (streamCap (ambient query) input (s.Q*s.r) p.headSize
    (CostAssembly.assembledWork k (ambient query) p)) (baseWidth 3 v.t) v.d v.t v.J

theorem queryStorageCap_polynomial {a : NodeNative.Data}
    (ha : Ready (Native.queryInputsAddressed query k hg first tail node) a)
    (input : ℕ) (hb : WordBound input a)
    (hv : query.Valid) (hn : 2 ≤ ambient query) (hs : SmallInputs query k (ambient query)) :
    queryStorageCap query k occurrence qi hg first tail node input ≤
      2560000000000000000*(input+1)^8*
        ((resources query k occurrence qi hg first tail).bits+1)^8*
        (CostAssembly.assembledWork k (ambient query) (resources query k occurrence qi hg first tail)+1)^8 := by
  let s := Native.queryInputsAddressed query k hg first tail node
  let p := resources query k occurrence qi hg first tail
  let work := CostAssembly.assembledWork k (ambient query) p
  let U := input+p.bits+work+2
  have hload := loaded_wordBound ha input hb
  have hload' : WordBound input (Native.project (loadedState a)) := fun i=>hload i
  have hinput : input ≤ U := by dsimp [U]; omega
  have hbitsU : p.bits+1 ≤ U := by dsimp [U]; omega
  have hworkU : work+1 ≤ U := by dsimp [U]; omega
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hnn : s.n ≤ input := by simpa [ha.heads.ambient,unary] using hload' 128
  have hR : s.R ≤ input := by simpa [ha.heads.order,unary] using hload' 138
  have hwidth : s.width.length ≤ input := by simpa [ha.heads.width] using hload' 140
  have hQr : s.Q*s.r ≤ input := by simpa [ha.heads.wordWidth,unary] using hload' 132
  have hbase : 0 < p.labelBase := by
    change 0 < 2*ambient query*matrixHeight query k+1
    omega
  have hheads : 1 ≤ p.heads := make_heads_pos query k occurrence _ _ _ _ _ _
  have hbits : 1 ≤ p.bits := make_bits_pos query k occurrence _ _ _ _ _ _
  have hhead := CostAssembly.headAssignments_le_assembledWork k (ambient query) p hbase hheads hbits
  have hj := FactorResource.produced_order_eq query k occurrence qi hg first tail hv
  have hsupport : SupportProgram.count s.n (produce (query.input k)).J ≤ work := by
    change SupportProgram.count (ambient query) (produce (query.input k)).J ≤ work
    rw [hj]
    exact CostAssembly.supportCount_le_assembledWork k (ambient query) p hbase hheads hbits
  obtain ⟨hna,hB,hd,hu,hjv⟩ :=
    FactorResource.produced_dimensions_le query k occurrence qi hg first tail hn hs
  have hdictionary := FactorResource.produced_seedBound_le query k occurrence qi
    (baseWidth 3 (produce (query.input k)).t) (produce (query.input k)).d
    (produce (query.input k)).t (produce (query.input k)).J p.bits hg first tail
    hj.le hna hB hd hu hjv
  have he : MomentsAssembly.dictionaryByteEnvelope (baseWidth 3 (produce (query.input k)).t)
      (produce (query.input k)).d (s.n+(produce (query.input k)).t+(produce (query.input k)).J)
      (MomentsAssembly.dictionaryCapacity (Finset.univ : Finset (Fin s.n))
        (produce (query.input k)).t (produce (query.input k)).J) ≤ 10*U^5 := by
    change FactorReady.seedBound (ambient query) _ _ _ _ ≤ _
    calc
      _ ≤ 10*(p.bits+1)^4*(work+1) := hdictionary
      _ ≤ 10*U^4*U := by gcongr
      _ = 10*U^5 := by ring
  apply polynomial_padding
  exact assignmentCap_polynomial s input p.headSize work _ _ _ _ U hU hinput
    (hnn.trans hinput) (hR.trans hinput) (hwidth.trans hinput) (hQr.trans hinput)
    (hhead.trans (by dsimp [U,work]; omega)) (by dsimp [U]; omega)
    (hsupport.trans (by dsimp [U]; omega)) he

end SubexponentialSAT.SqrtLog.NodeEnvelope

end

end OAI.Algorithms
