import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSourceBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceTerms

namespace OAI.Algorithms

/-! Bounds on every actual weight witness, uniform over retained exponents. -/

namespace SubexponentialSAT.SubexpMomentSourceProgram

open scoped BigOperators

def uniformDescriptorBudget (D B : ℕ) : ℕ :=
  D*(32*D^2+161*D+14*D*B+40*B+184)+
    SubexpWeightDescriptorProgram.retainedWeightBudget D B+
    173*B+12*D+32*SubexpSymbolicCost.indexBits D+117

def uniformCaptureBudget (D B : ℕ) : ℕ :=
  uniformDescriptorBudget D B+17*D*B+15*(1+(2*D+2)*D)+31

def uniformFrameBudget (D B : ℕ) : ℕ :=
  uniformCaptureBudget D B+40*SubexpSymbolicCost.indexBits D+160*B+82

def literalBytes (D B : ℕ) : ℕ := 4*SubexpSymbolicCost.indexBits D+16*B+7

theorem WeightResult.literal_length {ctx : Context} {a : Fin ctx.dimension → ℕ}
    {p : PointData ctx} (w : WeightResult ctx a p) :
    w.literal.length = literalBytes ctx.dimension ctx.target.length := by
  rw [WeightResult.literal,SubexpWeightLiteralProgram.rawLiteral_length]
  simp only [SubexpQuarticMarshal.marshalBits,List.length_append,List.length_replicate,w.length]
  unfold literalBytes
  omega

theorem descriptorBudget_le_uniform {ctx : Context} {a : Fin ctx.dimension → ℕ}
    (hc : ContextGood ctx a) (hdegree : (∑ i, a i) ≤ 2*ctx.dimension+1)
    {p : PointData ctx} (w : WeightResult ctx a p) :
    descriptorBudget ctx a p.support w.records ≤ uniformDescriptorBudget ctx.dimension ctx.target.length := by
  have hg := SubexpSourceBounds.retained_supportBudget_le a ctx.width ctx.target
    hc.padding hdegree p.support p.nodup
  have hw := SubexpWeightDescriptorProgram.goodRecords_scan_bound ctx.target.length a
    p.coordinates ctx.target p.support.reverse w.records w.good
      (by simpa only [List.nodup_reverse] using p.nodup) hdegree
  have hl := SubexpWeightLiteralProgram.overhead_le ctx.dimension ctx.target.length
  unfold descriptorBudget uniformDescriptorBudget
  omega

theorem PointData.bank_length {ctx : Context} (p : PointData ctx) :
    p.descriptor.bank.length = ctx.dimension*ctx.width.length := by
  change (List.ofFn p.coordinates).flatten.length = _
  rw [List.length_flatten,List.map_ofFn,Fin.sum_ofFn]
  simp [p.width]

theorem PointData.support_length_le {ctx : Context} (p : PointData ctx) :
    p.descriptor.support.length ≤ 1+(2*ctx.dimension+2)*ctx.dimension := by
  have h := Encoding.length_encodeList_upper id (SubexpWeightGather.supportBits p.support)
    ctx.dimension (by
      intro bits hbits
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbits
      simp only [id_eq,List.length_replicate]
      exact i.isLt.le)
  have hn : p.support.length ≤ ctx.dimension := by simpa using p.nodup.length_le_card
  change (Encoding.encodeList id (SubexpWeightGather.supportBits p.support)).length ≤ _
  simp only [SubexpWeightGather.supportBits,List.length_map] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hn) 1)

theorem captureBudget_le_uniform {ctx : Context} {a : Fin ctx.dimension → ℕ}
    (hc : ContextGood ctx a) (hdegree : (∑ i, a i) ≤ 2*ctx.dimension+1)
    {p : PointData ctx} (w : WeightResult ctx a p) :
    captureBudget ctx a p.coordinates p.support w.records ≤ uniformCaptureBudget ctx.dimension ctx.target.length := by
  have hd := descriptorBudget_le_uniform hc hdegree w
  have hb := p.bank_length
  have hs := p.support_length_le
  have hpad := Nat.mul_le_mul_left ctx.dimension hc.padding
  change (pointDescriptor p.coordinates p.support).bank.length = _ at hb
  change (pointDescriptor p.coordinates p.support).support.length ≤ _ at hs
  unfold captureBudget uniformCaptureBudget
  rw [hb]
  simp only [Nat.mul_assoc]
  omega

end SubexponentialSAT.SubexpMomentSourceProgram

end OAI.Algorithms
