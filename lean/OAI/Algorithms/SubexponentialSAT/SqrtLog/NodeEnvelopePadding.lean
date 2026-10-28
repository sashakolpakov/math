import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeQuery

namespace OAI.Algorithms

/-! A coefficient-free fixed padding envelope for the concrete assignment
consumer. The exponent absorbs only a fixed numeric constant. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.NodeEnvelope
open SubexponentialSAT MulticolorTypes SubexpSetupStorage
open LeafProgram LeafProgram.NodeNative LeafHeadSetupProgram ProducedQueryResources

theorem fixed_padding_bound (input V work : ℕ) (hV : 1 ≤ V) :
    2560000000000000000*(input+1)^8*(V+1)^8*(work+1)^8 ≤
      FactorResource.paddingEnvelope input V work 8 70 8 := by
  have hc : 2560000000000000000 ≤ (V+1)^62 := calc
    _ ≤ 2^62 := by norm_num
    _ ≤ (V+1)^62 := Nat.pow_le_pow_left (by omega) _
  calc
    _ ≤ (V+1)^62*(input+1)^8*(V+1)^8*(work+1)^8 := by gcongr
    _ = _ := by unfold FactorResource.paddingEnvelope; rw [show 70=62+8 by decide,pow_add]; ring

theorem queryStorageCap_padding (query : LeafQueryFrontend.Query) (k occurrence qi : ℕ)
    (hg : LeafParametersProgram.Guard (query.input k))
    (first : Word (problem query k hg).r (problem query k hg).Q)
    (tail : List (Word (problem query k hg).r (problem query k hg).Q))
    (node : Fin (problem query k hg).Q) {a : NodeNative.Data}
    (ha : Ready (Native.queryInputsAddressed query k hg first tail node) a)
    (input : ℕ) (hb : WordBound input a)
    (hv : query.Valid) (hn : 2 ≤ ambient query) (hs : SmallInputs query k (ambient query)) :
    queryStorageCap query k occurrence qi hg first tail node input ≤
      FactorResource.paddingEnvelope input (resources query k occurrence qi hg first tail).bits
        (CostAssembly.assembledWork k (ambient query) (resources query k occurrence qi hg first tail)) 8 70 8 :=
  (queryStorageCap_polynomial query k occurrence qi hg first tail node ha input hb hv hn hs).trans
    (fixed_padding_bound _ _ _ (make_bits_pos query k occurrence _ _ _ _ _ _))

end SubexponentialSAT.SqrtLog.NodeEnvelope

end

end OAI.Algorithms
