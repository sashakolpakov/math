import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBankFrame

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem emitterSize_le (a : Data) (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    emitterSize a ≤ 10*B := by
  have h67 := hB 67
  have h308 := hB 308
  have h309 := hB 309
  have h310 := hB 310
  have h71 := hB 71
  have h311 := hB 311
  have h312 := hB 312
  have h313 := hB 313
  have h314 := hB 314
  have h47 := hB 47
  unfold emitterSize
  omega

theorem stageTypes_cost_le (a : Data) (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    Staging.cost 0 1 stageTypesOps a ≤ 14*B+10 := by
  have h1 := hB 289
  have h2 := hB 292
  rw [stageTypes_cost]
  omega

theorem finishBound_le (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool)
    (positions : List ℕ) (a : Data) (B E : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B)
    (hE : UniversalRowSourceProgram.bound tables width rowWidth positions
      (deltaWord a) (a.stacks 47) (a.stacks 313) (a.stacks 314) ≤ E) :
    finishBound tables width rowWidth positions a B ≤ 224*B+E+271 := by
  have h23 := hB 23
  have h24 := hB 24
  have hs := emitterSize_le a B hB
  unfold finishBound
  omega

/-- Only a fixed linear staging overhead is added to the already measured
native table, mismatch and row-emitter budgets. -/
theorem universal_budget_le (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool)
    (positions : List ℕ) (a z : Data) (B V M E nv nm : ℕ)
    (ha : ∀ j,(a.stacks j).length ≤ B) (hz : ∀ j,(z.stacks j).length ≤ B)
    (hV : nv ≤ V) (hM : nm ≤ M)
    (hE : UniversalRowSourceProgram.bound tables width rowWidth positions
      (deltaWord z) (z.stacks 47) (z.stacks 313) (z.stacks 314) ≤ E) :
    Staging.cost 0 1 stageTypesOps a+nv+nm+finishBound tables width rowWidth positions z B ≤
      238*B+V+M+E+281 := by
  have hs := stageTypes_cost_le a B ha
  have hf := finishBound_le tables width rowWidth positions z B E hz hE
  omega

theorem literal_budget_le (a : Data) (src : Fin 320) (B : ℕ)
    (hB : (a.stacks src).length ≤ B) :
    14*(a.stacks src).length+19+120*B+180 ≤ 134*B+199 := by omega

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
