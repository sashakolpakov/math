import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorServices
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorFinish

namespace OAI.Algorithms

/-! Execution of the computed factor value and its multiplication into the
current head product. Input incidence dictionaries are the physically
produced tables supplied by the preceding service. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

theorem low_ne (i : Fin 56) (j : Fin 768) (hj : 56 ≤ j.val) :
    nativeStacks (Memory.lowPort i)  ≠  j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=j.val at hv
  omega

theorem indicatorStacks_low (i : Fin 56) :
    indicatorStacks (Memory.lowPort i)=nativeStacks (Memory.lowPort i) := by
  have h78 := low_ne i 78 (by decide)
  have h143 := low_ne i 143 (by decide)
  simp [indicatorStacks,Equiv.swap_apply_def,h78,h143]

omit [Fact (Nat.Prime p)] in
private theorem indicator_lowReady (ctx : Context p t n d) (a : Data)
    (rr : Fin 8 → Bool) (hash result : List Bool)
    (hlow : ∀ i,a.stacks (indicatorStacks (Memory.lowPort i))=low ctx i) :
    lowReady (FactorServices.indicatorFinished a rr hash result)
      (Product.idle ctx.modulus.bits ctx.width ctx.cache.zero.val
        (RingTriple.tableEncoding ctx.table) (List.replicate d true)
        (List.replicate ctx.u true) (List.replicate ctx.J true)) := by
  intro i
  rw [FactorServices.indicator_frame _ _ _ _ _ (low_ne i 64 (by decide))
    (low_ne i 67 (by decide)) (low_ne i 68 (by decide))]
  simpa only [indicatorStacks_low, low] using hlow i

/-- The native indicator is applied to the actual expanded row, then its
result is multiplied into151. The old hash and incidence table are cleared. -/
theorem hash_value_eval (ctx : Context p t n d) (hd : 0 < d) (hB : 0 < baseWidth p t)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool))
    (hl : ∀ v : Fin n,entries.lookup (Encoding.encodeNat v.val)=some (Product.bytes (incidence v)))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (a : Data)
    (hlow : ∀ i,a.stacks (indicatorStacks (Memory.lowPort i))=low ctx i)
    (hsource : a.stacks 64=Encoding.encodeList id (ws.map Row.payload))
    (htable : a.stacks 62=Squarefree.Program.lookupRecords entries)
    (hone : a.stacks 69=Product.bytes one) (hminus : a.stacks 76=RingProgram.flat minus)
    (htape : a.stacks 143=IdempotentApplyProgram.triplesTape digits)
    (hshape : (a.stacks 88).length=n)
    (hwork : ∀ i ∈ FactorServices.indicatorScratch,a.stacks (indicatorStacks i)=[])
    (hseed : a.stacks 151=Product.bytes seed) (htmp : a.stacks 159=[]) :
    let factor := Indicator.result ctx minus one incidence ws digits
    let result := Product.run p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor []
    ∃ k b,k ≤ FactorServices.indicatorBudget ctx minus one incidence entries ws digits+
        (2*(Product.bytes (Indicator.rawHash ctx minus one incidence ws)).length+
          2*(a.stacks 62).length+6+productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor) ∧
      Eval (.seq indicator (.seq (clear 68) (.seq (clear 62) accumulate))) k a b ∧
      b.stacks=Function.update (Function.update (Function.update (Function.update
        (Function.update a.stacks 64 []) 67 []) 68 []) 62 []) 151 (Product.bytes result) := by
  dsimp only
  obtain ⟨ki,ri,hki,hi⟩ := FactorServices.indicator_eval ctx hd hB minus one incidence entries hl
    ws digits a hlow hsource htable hone hminus htape hshape hwork
  let mid := FactorServices.indicatorFinished a ri
    (Product.bytes (Indicator.rawHash ctx minus one incidence ws))
    (Product.bytes (Indicator.result ctx minus one incidence ws digits))
  have h61 : a.stacks 61=[] := by
    simpa only [show indicatorStacks 61 = 61 by decide] using hwork 61 (by decide)
  have h70 : a.stacks 70=[] := by
    simpa only [show indicatorStacks 70 = 70 by decide] using hwork 70 (by decide)
  obtain ⟨kt,b,hkt,ht,hb⟩ := hash_tail_eval p t ctx.modulus ctx.cache ctx.zeroBound ctx.table
    (List.replicate d true) ctx.width (by simp) ctx.widthLength ctx.u ctx.J seed
    (Indicator.result ctx minus one incidence ws digits) mid
    (indicator_lowReady ctx a ri _ _ hlow)
    (by simpa [mid,FactorServices.indicatorFinished] using hseed)
    (by simp [mid,FactorServices.indicatorFinished])
    (by simpa [mid,FactorServices.indicatorFinished] using h61)
    (by simpa [mid,FactorServices.indicatorFinished] using h70)
    (by simpa [mid,FactorServices.indicatorFinished] using htmp)
  have hm68 : mid.stacks 68=Product.bytes (Indicator.rawHash ctx minus one incidence ws) := by
    simp [mid,FactorServices.indicatorFinished]
  have hm62 : mid.stacks 62=a.stacks 62 := by simp [mid,FactorServices.indicatorFinished]
  rw [hm68,hm62] at hkt
  refine ⟨ki+kt,b,by omega,hi.seq ht,?_⟩
  rw [hb]
  funext i
  by_cases h64 : i=64 <;> by_cases h67 : i=67 <;> by_cases h68 : i=68 <;>
    by_cases h62 : i=62 <;> by_cases h151 : i=151 <;>
    simp [mid,FactorServices.indicatorFinished,h64,h67,h68,h62,h151]


omit [Fact (Nat.Prime p)] in
private theorem clause_lowReady (ctx : Context p t n d) (a : Data)
    (rr : Fin 8 → Bool) (result : List Bool)
    (hlow : ∀ i,a.stacks (Clause.callerStacks (Memory.lowPort i))=low ctx i) :
    lowReady (FactorServices.clauseFinished a rr result)
      (Product.idle ctx.modulus.bits ctx.width ctx.cache.zero.val
        (RingTriple.tableEncoding ctx.table) (List.replicate d true)
        (List.replicate ctx.u true) (List.replicate ctx.J true)) := by
  intro i
  rw [FactorServices.clause_frame _ _ _ _ (low_ne i 63 (by decide)) (low_ne i 67 (by decide))]
  exact hlow i

/-- The marked clause is evaluated directly and multiplied once. It does
not pass through the hash idempotent. -/
theorem marked_value_eval (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool))
    (hl : ∀ v : Fin n,entries.lookup (Encoding.encodeNat v.val)=some (Product.bytes (incidence v)))
    (ls : List (SAT.Literal (Fin n))) (a : Data)
    (hlow : ∀ i,a.stacks (Clause.callerStacks (Memory.lowPort i))=low ctx i)
    (hsource : a.stacks 63=Encoding.encodeList id (ls.map HashCircuitProgram.Native.Clause.literalBits))
    (htable : a.stacks 62=Squarefree.Program.lookupRecords entries)
    (hone : a.stacks 69=Product.bytes one) (hminus : a.stacks 76=RingProgram.flat minus)
    (hwork : ∀ i ∈ FactorServices.clauseScratch,a.stacks (Clause.callerStacks i)=[])
    (hseed : a.stacks 151=Product.bytes seed) (htmp : a.stacks 159=[]) :
    let factor := FactorServices.clauseResult ctx minus one incidence ls
    let result := Product.run p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor []
    ∃ k b,k  ≤  FactorServices.clauseBudget ctx minus one incidence entries ls+
        (2*(a.stacks 62).length+3+productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor) ∧
      Eval (.seq Clause.caller (.seq (clear 62) accumulate)) k a b ∧
      b.stacks=Function.update (Function.update (Function.update
        (Function.update a.stacks 63 []) 67 []) 62 []) 151 (Product.bytes result) := by
  dsimp only
  obtain ⟨ki,ri,hki,hi⟩ := FactorServices.clause_eval ctx minus one incidence entries hl ls a
    hlow hsource htable hone hminus hwork
  let mid := FactorServices.clauseFinished a ri (Product.bytes (FactorServices.clauseResult ctx minus one incidence ls))
  have h61 : a.stacks 61=[] := hwork 61 (by decide)
  have h70 : a.stacks 70=[] := hwork 70 (by decide)
  obtain ⟨kt,b,hkt,ht,hb⟩ := marked_tail_eval p t ctx.modulus ctx.cache ctx.zeroBound ctx.table
    (List.replicate d true) ctx.width (by simp) ctx.widthLength ctx.u ctx.J seed
    (FactorServices.clauseResult ctx minus one incidence ls) mid
    (clause_lowReady ctx a ri _ hlow)
    (by simpa [mid,FactorServices.clauseFinished] using hseed)
    (by simp [mid,FactorServices.clauseFinished])
    (by simpa [mid,FactorServices.clauseFinished] using h61)
    (by simpa [mid,FactorServices.clauseFinished] using h70)
    (by simpa [mid,FactorServices.clauseFinished] using htmp)
  have hm62 : mid.stacks 62=a.stacks 62 := by simp [mid,FactorServices.clauseFinished]
  rw [hm62] at hkt
  refine ⟨ki+kt,b,by omega,hi.seq ht,?_⟩
  rw [hb]
  funext i
  by_cases h63 : i=63 <;> by_cases h67 : i=67 <;> by_cases h62 : i=62 <;> by_cases h151 : i=151 <;>
    simp [mid,FactorServices.clauseFinished,h63,h67,h62,h151]

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
