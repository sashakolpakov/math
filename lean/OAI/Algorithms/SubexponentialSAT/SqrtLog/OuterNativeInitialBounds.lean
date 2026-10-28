import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeDeterminism
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramInitialResource

namespace OAI.Algorithms

/-! The actual initial-code bound holds for every observed trace, with literal
padded output words. This closes the universal-run quantifier in HistorySupply. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage Filter LeafOuterProgram
open scoped Topology

 theorem eventually_observed_initialCode_bound :
    ∃ C d p : ℕ, ∀ q : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ (a : Data) W (records : List (List Bool)) B,
      WordBound W a → (∀ i : Fin 896, i.val ≤ 782 → a.stacks i=[]) →
      a.stacks 784=Encoding.encodeList id records → records≠[] →
      0 < B → BinaryArithmetic.toNat (a.stacks 786)=B →
      BinaryArithmetic.toNat (a.stacks 785)=n →
      records.length ≤ n*B → B ≤ Asymptotic.L n^q →
      ∀ steps b, Eval initialCode steps a b →
      steps ≤ CodeSetupOuterCost.setupMajorant C d q n*(W+1)^p ∧
      WordBound (W+CodeSetupOuterCost.setupMajorant C d q n*(W+1)^p) b := by
  obtain ⟨C,d,p,h⟩ := initialCode_resource_eval
  refine ⟨C,d,p,?_⟩
  intro q
  filter_upwards [h q] with n hn
  intro a W records B ha he hf hm hB hv hnv hcount hBL steps b hb
  obtain ⟨t,c,s,Q,hc,ht,_⟩ := hn a W records B ha he hf hm hB hv hnv hcount hBL
  exact observed_wordBound 0 ha hb hc ht

end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
