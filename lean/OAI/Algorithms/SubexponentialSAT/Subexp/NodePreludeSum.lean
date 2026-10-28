import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.NodeCacheBounds
import OAI.Algorithms.SubexponentialSAT.SubexpNodePreludeBound
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBasisExecution

namespace OAI.Algorithms

/-! One explicit envelope for the actual per-node stages before packet and
template construction. The inputs are physical states and checked structural
relations; no numerical execution-cost cap is assumed. -/
namespace SubexponentialSAT.Subexp.NodePreludeSum

open GlobalBasisInput (Context Location)

def scale (p D m C R N B b modulusLen : ℕ) [Fact p.Prime]
    (cacheState : SubexpNodeCacheSetup.Data) (query : List Bool) (nodes : List (List Bool))
    (basisState bankState : StructuredProgram.State 16 288) : ℕ :=
  NodeCacheBounds.scale m C R N B b modulusLen +
    SubexpNodePreludeBound.cacheInputSize cacheState +
    SubexpNodePreludeBound.indexSize query nodes +
    (SubexpNodeBasisExecution.inputVolume basisState+2) +
    SubexpNodePreludeBound.bankInputSize p D bankState+1

/-- The exact six-term prelude budget, including each specified outer halt. -/
def cost {p r Q Δ D : ℕ} [Fact p.Prime]
    (m C R N B b modulusLen : ℕ) (cacheState : SubexpNodeCacheSetup.Data)
    (query : List Bool) (nodes : List (List Bool))
    (ctx : Context p r Q Δ) (count leftovers : ℕ) (locs : List (Location r Q Δ))
    (basisState bankState : StructuredProgram.State 16 288)
    (matrices : List (SubexpNodeBankMap.Matrix p D)) : ℕ :=
  SubexpNodeCacheSetup.prepareCost cacheState +
    (SubexpTaylorCacheMap.tableBudget m C (R+1) N B+1) +
    (SubexpNodeIndexProgram.budget query nodes+1) +
    SubexpNodeBasisExecution.runtimeBound ctx count leftovers locs basisState +
    (SubexpNodeBankStage.budget bankState matrices+1) +
    (SubexpOriginMap.tableBound m C B b modulusLen (N-1)+1)

section Layout

variable {p D k Δ r Q : ℕ} {τ : ℚ} [Fact p.Prime]
variable {F E : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E]
variable {P : Factor.Pattern (Fin D) F} {c : SubexpLayoutSpec.Parameters p k Δ r τ}
variable {L : SubexpLayoutSpec.Layout (E := E) P c} {t : Fin c.Q}

/-- Complete cache preparation, Taylor table, index, basis, bank generation,
and origin extraction. The basis and matrix premises describe actual encoded
inputs and arrays, rather than bounding their execution costs. -/
theorem cost_le (e : SubexpLayoutSpec.EnumerationData L t)
    (matrices : List (SubexpNodeBankMap.Matrix p D))
    (harrays : matrices.map (fun M => MatrixImageEnumeration.bankRecords p M.entries) =
      SubexpNodeBankBounds.outerBanks e :: SubexpNodeBankBounds.innerBanks e)
    (m C R N B b modulusLen : ℕ) (cacheState : SubexpNodeCacheSetup.Data)
    (query : List Bool) (nodes : List (List Bool))
    (ctx : Context p r Q Δ) (count leftovers : ℕ) (locs : List (Location r Q Δ))
    (before : List (List Bool)) (tail : List Bool)
    (basisState bankState : StructuredProgram.State 16 288)
    (H : SubexpNodeBasisExecution.Input ctx count leftovers locs.length before tail basisState)
    (hlocs : ctx.locations 0 locs) :
    cost m C R N B b modulusLen cacheState query nodes ctx count leftovers locs
      basisState bankState matrices ≤
      100000000000000000000 *
        (scale p D m C R N B b modulusLen cacheState query nodes basisState bankState)^20 *
        (e.iterationCount+1)^4 := by
  let S := scale p D m C R N B b modulusLen cacheState query nodes basisState bankState
  let J := (e.iterationCount+1)^4
  let T := S^20*J
  have hS : 1 ≤ S := by dsimp [S,scale]; omega
  have hJ : 1 ≤ J := Nat.one_le_pow _ _ (by omega)
  have hpower (x a : ℕ) (hx : x ≤ S) (ha : a ≤ 20) : x^a ≤ S^20 :=
    (Nat.pow_le_pow_left hx a).trans (Nat.pow_le_pow_right hS ha)
  have hST : S^20 ≤ T := by
    simpa only [T,mul_one] using Nat.mul_le_mul_left (S^20) hJ
  have hT : 1 ≤ T := (Nat.one_le_pow _ _ hS).trans hST
  have hparam : NodeCacheBounds.scale m C R N B b modulusLen ≤ S := by
    dsimp [S,scale]
    omega
  have hcacheSize : SubexpNodePreludeBound.cacheInputSize cacheState ≤ S := by
    dsimp [S,scale]
    omega
  have hindexSize : SubexpNodePreludeBound.indexSize query nodes ≤ S := by
    dsimp [S,scale]
    omega
  have hbasisSize : SubexpNodeBasisExecution.inputVolume basisState+2 ≤ S := by
    dsimp [S,scale]
    omega
  have hbankSize : SubexpNodePreludeBound.bankInputSize p D bankState ≤ S := by
    dsimp [S,scale]
    omega
  have hcacheT : SubexpNodePreludeBound.cacheInputSize cacheState ≤ T := by
    have h := (hpower _ 1 hcacheSize (by decide)).trans hST
    simpa only [pow_one] using h
  have hcache : SubexpNodeCacheSetup.prepareCost cacheState ≤ 45*T :=
    (SubexpNodePreludeBound.cache_prepare_le cacheState).trans
      (Nat.mul_le_mul_left 45 hcacheT)
  have htaylor : SubexpTaylorCacheMap.tableBudget m C (R+1) N B ≤ 4001616*T :=
    (NodeCacheBounds.tableBudget_le m C R N B b modulusLen).trans
      (Nat.mul_le_mul_left 4001616 ((hpower _ 6 hparam (by decide)).trans hST))
  have hindex : SubexpNodeIndexProgram.budget query nodes+1 ≤ 90*T :=
    (SubexpNodePreludeBound.index_budget_le query nodes).trans
      (Nat.mul_le_mul_left 90 ((hpower _ 2 hindexSize (by decide)).trans hST))
  have hbasis0 := SubexpNodeBasisExecution.runtimeBound_le_inputBudget
    ctx count leftovers locs before tail basisState H hlocs
  have hbasis : SubexpNodeBasisExecution.runtimeBound ctx count leftovers locs basisState ≤
      1000000000000000099*T := by
    apply hbasis0.trans
    unfold SubexpNodeBasisExecution.inputBudget
    exact Nat.mul_le_mul_left _ ((hpower _ 20 hbasisSize le_rfl).trans hST)
  have hbank0 := SubexpNodePreludeBound.bank_budget_le e matrices harrays bankState
  have hbank : SubexpNodeBankStage.budget bankState matrices+1 ≤ 100100*T := by
    have h := hbank0.trans (Nat.mul_le_mul_right J
      (Nat.mul_le_mul_left 100100 (hpower _ 3 hbankSize (by decide))))
    simpa only [T,Nat.mul_assoc] using h
  have horigin : SubexpOriginMap.tableBound m C B b modulusLen (N-1) ≤ 5580*T :=
    (NodeCacheBounds.originTableBound_le m C R N B b modulusLen).trans
      (Nat.mul_le_mul_left 5580 ((hpower _ 4 hparam (by decide)).trans hST))
  have hsum : cost m C R N B b modulusLen cacheState query nodes ctx count leftovers locs
      basisState bankState matrices ≤ 100000000000000000000*T := by
    unfold cost
    omega
  calc
    _ ≤ 100000000000000000000*T := hsum
    _ = _ := by dsimp [T,S,J]; ring

end Layout
end SubexponentialSAT.Subexp.NodePreludeSum

#print axioms SubexponentialSAT.Subexp.NodePreludeSum.cost_le

end OAI.Algorithms
