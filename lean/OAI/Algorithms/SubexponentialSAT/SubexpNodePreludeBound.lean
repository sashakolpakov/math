import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBankRuntimeBound
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBankStage
import OAI.Algorithms.SubexponentialSAT.SubexpNodeIndexProgram
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCacheSetup

namespace OAI.Algorithms

/-! Actual copy, index, and bank-stage costs before template construction.
The size variables list the exact original words read by those stages. -/

namespace SubexponentialSAT.SubexpNodePreludeBound

open BitProgram StructuredCalls

def indexSize (query : List Bool) (nodes : List (List Bool)) : ℕ :=
  query.length + (ProgramEncoding.encodeRecords nodes).length + 1

theorem index_budget_le (query : List Bool) (nodes : List (List Bool)) :
    SubexpNodeIndexProgram.budget query nodes + 1 ≤ 90 * (indexSize query nodes)^2 := by
  let S := indexSize query nodes
  have hS : 1 ≤ S := by dsimp [S, indexSize]; omega
  have hq : query.length ≤ S := by dsimp [S, indexSize]; omega
  have hm : (ProgramEncoding.encodeRecords nodes).length + 1 ≤ S := by dsimp [S, indexSize]; omega
  have hb : 9 * query.length + 80 ≤ 89 * S := by omega
  have hp := Nat.mul_le_mul hb hm
  change (9 * query.length + 80) * ((ProgramEncoding.encodeRecords nodes).length + 1) + 1 ≤ 90 * S^2
  nlinarith only [hp, hS]

def cacheInputSize (d : SubexpNodeCacheSetup.Data) : ℕ :=
  (d.stacks 255).length + (d.stacks 126).length + (d.stacks 5).length +
    (d.stacks 91).length + (d.stacks 10).length + 1

theorem cache_prepare_le (d : SubexpNodeCacheSetup.Data) :
    SubexpNodeCacheSetup.prepareCost d ≤ 45 * cacheInputSize d := by
  unfold SubexpNodeCacheSetup.prepareCost cacheInputSize
  omega

def cleanupInputSize (d : SubexpNodeCacheSetup.Data) : ℕ :=
  (d.stacks 100).length + (d.stacks 101).length + (d.stacks 66).length +
    (d.stacks 73).length + (d.stacks 74).length + (d.stacks 81).length +
    (d.stacks 78).length + (d.stacks 102).length + 1

theorem cache_cleanup_le (d : SubexpNodeCacheSetup.Data) :
    SubexpNodeCacheSetup.cleanupCost d ≤ 24 * cleanupInputSize d := by
  unfold SubexpNodeCacheSetup.cleanupCost cleanupInputSize
  omega

def bankInputSize (p D : ℕ) [Fact p.Prime] (d : StructuredProgram.State 16 288) : ℕ :=
  SubexpNodeBankRuntimeBound.scale p D +
    (d.stacks 279).length + (d.stacks 277).length + (d.stacks 280).length + (d.stacks 264).length + 1

theorem bank_copy_cost (d : StructuredProgram.State 16 288) :
    SubexpNodeBasisStage.copyCost SubexpNodeBankStage.moves d =
      7 * ((d.stacks 279).length + (d.stacks 277).length +
        (d.stacks 280).length + (d.stacks 264).length) + 20 := by
  simp [SubexpNodeBasisStage.copyCost, SubexpNodeBankStage.moves,
    SubexpScanPrimitives.afterCopy, StackRoutines.copyStacks]
  omega

variable {p D k Δ r : ℕ} {τ : ℚ} [Fact p.Prime]
variable {F E : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E]
variable {P : Factor.Pattern (Fin D) F} {c : SubexpLayoutSpec.Parameters p k Δ r τ}
variable {L : SubexpLayoutSpec.Layout (E := E) P c} {t : Fin c.Q}

/-- Includes the four physical input copies, mapper, four clears, and
compiled halt. The exact bank-array identity is supplied by the computed
global enumeration, not a numeric cost assumption. -/
theorem bank_budget_le (e : SubexpLayoutSpec.EnumerationData L t)
    (matrices : List (SubexpNodeBankMap.Matrix p D))
    (harrays : matrices.map (fun M => Subexp.MatrixImageEnumeration.bankRecords p M.entries) =
      SubexpNodeBankBounds.outerBanks e :: SubexpNodeBankBounds.innerBanks e)
    (d : StructuredProgram.State 16 288) :
    SubexpNodeBankStage.budget d matrices + 1 ≤
      100100 * (bankInputSize p D d)^3 * (e.iterationCount + 1)^4 := by
  let S := bankInputSize p D d
  let J := e.iterationCount + 1
  have hS : 1 ≤ S := by dsimp [S, bankInputSize]; omega
  have hJ : 1 ≤ J := by dsimp [J]; omega
  have hscale : SubexpNodeBankRuntimeBound.scale p D ≤ S := by dsimp [S, bankInputSize]; omega
  have hcommon : SubexpNodeBankMap.commonSize p D ≤ S := by
    dsimp [S, bankInputSize, SubexpNodeBankRuntimeBound.scale]
    omega
  have hcopies : (d.stacks 279).length + (d.stacks 277).length +
      (d.stacks 280).length + (d.stacks 264).length ≤ S := by dsimp [S, bankInputSize]; omega
  have hb := (SubexpNodeBankRuntimeBound.runtimeBound_le_iterations e matrices harrays).trans
    (Nat.mul_le_mul_right (J^4) (Nat.mul_le_mul_left 100000 (Nat.pow_le_pow_left hscale 3)))
  have hsmall : S ≤ S^3 * J^4 := by
    calc
      S = S * 1 := by omega
      _ ≤ S^3 * J^4 := Nat.mul_le_mul (Nat.le_self_pow (by decide) S) (Nat.one_le_pow 4 J hJ)
  unfold SubexpNodeBankStage.budget SubexpNodeBankStage.cleanupBound
  rw [bank_copy_cost]
  change _ ≤ 100100 * S^3 * J^4
  nlinarith only [hb, hcommon, hcopies, hsmall, hS]

end SubexponentialSAT.SubexpNodePreludeBound

end OAI.Algorithms
