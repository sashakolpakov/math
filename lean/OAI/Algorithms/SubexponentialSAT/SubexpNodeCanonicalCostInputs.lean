import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodePreludeBound
import OAI.Algorithms.SubexponentialSAT.SubexpNodeOriginalInputBound
import OAI.Algorithms.SubexponentialSAT.SubexpNodeContexts

namespace OAI.Algorithms

/-! Remove mutable-workspace quantities from the numerical bounds using
the actual canonical store equations of the node worker. -/

namespace SubexponentialSAT.SubexpNodeCanonicalCostInputs

open SubexpNodeWorkspace SubexpNodeStoreTransitions SubexpNodeContexts
open SubexpNodePreludeBound SubexpNodeWorkerBound
open SubexpMomentSourceInputBounds SubexpSymbolicCost

attribute [local simp] Fin.coe_ofNat_eq_mod

def sourceScale (p D : ℕ) (masters : Store) (index : List Bool) : ℕ :=
  (D + (masters 129).length + (masters 10).length + indexBits D +
    (masters 122).length + (masters 123).length + 1) +
  parameterSize D 4 (Nat.log 2 p + 1) + SubexpNodeJobsCostBound.scale D (indexBits D) +
  (D + indexBits D + (masters 129).length + (masters 10).length +
    (masters 5).length + (masters 124).length + (masters 122).length + (masters 123).length) +
  index.length + 1

theorem suffixSize_eq (p D : ℕ) (masters : Store) (index template : List Bool)
    (d : SubexpNodeWorkerBound.Data) (h : d.stacks = templated masters index template) :
    suffixSize p (sourceContext masters D template) d = sourceScale p D masters index := by
  simp [suffixSize, sizeParameter, sourceContext, SubexpNodeJobsReady.contextSize,
    h, templated, initialStacks, MasterPort, sourceScale]

theorem cacheInputSize_eq (masters : Store) (node : List Bool)
    (d : SubexpNodeCacheSetup.Data)
    (h : d.stacks = activeStacks masters node ∘ Fin.castAdd 32) :
    cacheInputSize d = (masters 255).length + (masters 126).length + (masters 5).length +
      (masters 91).length + (masters 10).length + 1 := by
  simp [cacheInputSize, h, activeStacks, initialStacks, MasterPort]

theorem cleanupInputSize_eq (masters : Store) (node cache index blueprint : List Bool)
    (d : SubexpNodeCacheSetup.Data)
    (h : d.stacks = raw masters node cache index blueprint ∘ Fin.castAdd 32) :
    cleanupInputSize d = (masters 255).length + (masters 126).length + (masters 5).length +
      (masters 91).length + 5 * (masters 10).length + node.length + cache.length + 1 := by
  simp [cleanupInputSize, h, raw, indexed, cached, activeStacks,
    SubexpNodeCacheSetup.width4]
  omega

theorem indexed_scratch226 (masters : Store) (node cache index : List Bool) :
    indexed masters node cache index 226 = [] := by rfl

/-- The raw-template cleanup's old scratch word is empty on the actual
path. The bank/origin stage and packet updates preserve this fact. -/
theorem packet_scratch (masters : Store) (node cache index banks origins packets : List Bool) :
    let s := Function.update (Function.update
      (SubexpNodeBasisBankOrigin.finishedStacks (indexed masters node cache index) banks origins)
        227 []) 225 packets
    s 226 = [] ∧ s 227 = [] := by
  exact ⟨rfl, rfl⟩

theorem bankInputSize_eq (p D : ℕ) [Fact p.Prime] (masters : Store)
    (d : StructuredProgram.State 16 288)
    (h279 : d.stacks 279 = masters 279) (h277 : d.stacks 277 = masters 277)
    (h280 : d.stacks 280 = masters 280) (h264 : d.stacks 264 = masters 264) :
    bankInputSize p D d = SubexpNodeBankRuntimeBound.scale p D +
      (masters 279).length + (masters 277).length + (masters 280).length +
      (masters 264).length + 1 := by
  simp only [bankInputSize, h279, h277, h280, h264]

end SubexponentialSAT.SubexpNodeCanonicalCostInputs

end OAI.Algorithms
