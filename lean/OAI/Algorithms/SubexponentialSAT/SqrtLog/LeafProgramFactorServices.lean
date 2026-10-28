import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorServicesBase

namespace OAI.Algorithms

/-! Actual wide factor service calls, including the indicator's three parser
register writes, compiled returns, and exact caller frame. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorServices
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps
open MomentsProgram

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod Fin.ext_iff

variable {p t n d : ℕ} [Fact p.Prime]

def indicatorBudget (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t))) : ℕ :=
  11+DynamicFold.work Row.payload
    (Row.value p t ctx.modulus ctx.cache ctx.table minus one incidence ctx.u ctx.J)
    (Row.cost p t ctx.modulus ctx.cache ctx.table minus one incidence
      (List.replicate d true) ctx.u ctx.J entries) ws []+
    IdempotentApplyProgram.applicationBudget ctx minus (Indicator.rawHash ctx minus one incidence ws) one digits

theorem indicator_eval (ctx : Context p t n d) (hd : 0 < d) (hB : 0 < baseWidth p t)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool))
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val)=some (Product.bytes (incidence v)))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (a : Factor.Data)
    (hlow : ∀ i, a.stacks (Factor.indicatorStacks (Memory.lowPort i))=low ctx i)
    (hsource : a.stacks 64=Encoding.encodeList id (ws.map Row.payload))
    (htable : a.stacks 62=Squarefree.Program.lookupRecords entries)
    (hone : a.stacks 69=Product.bytes one) (hminus : a.stacks 76=RingProgram.flat minus)
    (htape : a.stacks 143=IdempotentApplyProgram.triplesTape digits)
    (hshape : (a.stacks 88).length=n)
    (hwork : ∀ i∈indicatorScratch,a.stacks (Factor.indicatorStacks i)=[]) :
    ∃ k rr, k ≤ indicatorBudget ctx minus one incidence entries ws digits ∧
      Eval Factor.indicator k a (indicatorFinished a rr
        (Product.bytes (Indicator.rawHash ctx minus one incidence ws))
        (Product.bytes (Indicator.result ctx minus one incidence ws digits))) := by
  let h := high Factor.indicatorStacks a
  let source := Encoding.encodeList id (ws.map Row.payload)
  have hready : IdempotentApplyProgram.Multiplier.ready h := by
    intro i hi
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals (apply hwork; decide)
  have hinput : Memory.tapes (low ctx) (Row.recordHigh h [] source [])=a.stacks ∘ Factor.indicatorStacks := by
    rw [row_high_input Factor.indicatorStacks a source hsource hwork]
    exact input_tapes Factor.indicatorStacks a (low ctx) hlow
  obtain ⟨k,rr,hk,he⟩ := Indicator.command_eval ctx hd hB minus one incidence entries hl ws digits
    (a.regs ∘ Factor.nativeRegisters) h
    (by exact htable) (by exact hone) (by exact hminus) (by exact htape)
    (by exact hwork 79 (by decide)) (by exact hshape) hready
  have hproject : projectState Factor.nativeRegisters Factor.indicatorStacks (readied a)=
      RecordPrograms.state rowPorts
        (Row.base (a.regs ∘ Factor.nativeRegisters)
          (Product.idle ctx.modulus.bits ctx.width ctx.cache.zero.val
            (RingTriple.tableEncoding ctx.table) (List.replicate d true)
            (List.replicate ctx.u true) (List.replicate ctx.J true)) h [])
        false true false source [] := by
    rw [Row.record_state]
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [readied,Factor.nativeRegisters]
    · exact hinput.symm
  dsimp only [source] at hproject
  rw [← hproject] at he
  have hc := eval_liftCommand_from_state Indicator.command 64 67 Factor.nativeRegisters
    Factor.indicatorStacks (readied a) Factor.nativeRegisters_injective Factor.indicatorStacks_injective he
  rw [indicator_embed a rr (low ctx) source _ _ hinput] at hc
  refine ⟨3+(k+1),rr,?_,(ready_eval a).seq hc⟩
  unfold indicatorBudget
  omega

def clauseBudget (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool)) (ls : List (SAT.Literal (Fin n))) : ℕ :=
  7*(Product.bytes one).length+9+
    DynamicFold.work HashCircuitProgram.Native.Clause.literalBits
      (HashCircuitProgram.Native.Clause.step p t ctx.modulus ctx.cache ctx.table minus one incidence ctx.u ctx.J)
      (HashCircuitProgram.Native.Clause.cost p t ctx.modulus ctx.cache ctx.table minus one incidence
        (List.replicate d true) ctx.u ctx.J entries) ls one

def clauseResult (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d)) (ls : List (SAT.Literal (Fin n))) :=
  DynamicFold.value (HashCircuitProgram.Native.Clause.step p t ctx.modulus ctx.cache ctx.table
    minus one incidence ctx.u ctx.J) ls one

theorem clause_eval (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool))
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val)=some (Product.bytes (incidence v)))
    (ls : List (SAT.Literal (Fin n))) (a : Factor.Data)
    (hlow : ∀ i, a.stacks (Clause.callerStacks (Memory.lowPort i))=low ctx i)
    (hsource : a.stacks 63=Encoding.encodeList id (ls.map HashCircuitProgram.Native.Clause.literalBits))
    (htable : a.stacks 62=Squarefree.Program.lookupRecords entries)
    (hone : a.stacks 69=Product.bytes one) (hminus : a.stacks 76=RingProgram.flat minus)
    (hwork : ∀ i∈clauseScratch,a.stacks (Clause.callerStacks i)=[]) :
    ∃ k rr, k ≤ clauseBudget ctx minus one incidence entries ls ∧
      Eval Clause.caller k a (clauseFinished a rr
        (Product.bytes (clauseResult ctx minus one incidence ls))) := by
  let h := high Clause.callerStacks a
  let source := Encoding.encodeList id (ls.map HashCircuitProgram.Native.Clause.literalBits)
  have hinput : Memory.tapes (low ctx) (HashCircuitProgram.Native.Clause.recordHigh h [] source [])=
      a.stacks ∘ Clause.callerStacks := by
    rw [clause_high_input Clause.callerStacks a source hsource hwork]
    exact input_tapes Clause.callerStacks a (low ctx) hlow
  obtain ⟨k,rr,hk,he⟩ := Clause.command_eval p t ctx.modulus ctx.cache ctx.zeroBound ctx.table
    minus one incidence (List.replicate d true) ctx.width ctx.u ctx.J (by simp) ctx.widthLength
    entries hl (a.regs ∘ Clause.callerRegisters) h
    (by exact htable) (by exact hone) (by exact hminus) (by exact hwork 70 (by decide)) ls
  have hproject : projectState Clause.callerRegisters Clause.callerStacks a=
      Memory.state (a.regs ∘ Clause.callerRegisters) (low ctx)
        (HashCircuitProgram.Native.Clause.recordHigh h [] source []) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · exact hinput.symm
  dsimp only [low,source] at hproject
  rw [← hproject,HashCircuitProgram.Native.Clause.record_state] at he
  let rf := Function.update (Function.update (Function.update rr 0 false) 1 true) 2 false
  have hc := eval_liftCommand_from_state Clause.command 63 67 Clause.callerRegisters
    Clause.callerStacks a (Fin.castAdd_injective 8 32) (Fin.castAdd_injective 96 672) he
  change Eval (liftCommand Clause.command 63 67 Clause.callerRegisters Clause.callerStacks) (k+1) a
    (embedState Clause.callerRegisters Clause.callerStacks a
      (Memory.state rf (low ctx) (HashCircuitProgram.Native.Clause.recordHigh
        (high Clause.callerStacks a) (Product.bytes (clauseResult ctx minus one incidence ls)) [] []))) at hc
  rw [clause_embed a rf (low ctx) source (Product.bytes (clauseResult ctx minus one incidence ls)) hinput] at hc
  exact ⟨k+1,rf,by dsimp [clauseBudget] at *; omega,hc⟩

theorem indicator_frame (a : Factor.Data) (rr : Fin 8 → Bool) (hash result : List Bool)
    (i : Fin 768) (h64 : i≠64) (h67 : i≠67) (h68 : i≠68) :
    (indicatorFinished a rr hash result).stacks i=a.stacks i := by
  simp [indicatorFinished,h64,h67,h68]

theorem clause_frame (a : Factor.Data) (rr : Fin 8 → Bool) (result : List Bool)
    (i : Fin 768) (h63 : i≠63) (h67 : i≠67) :
    (clauseFinished a rr result).stacks i=a.stacks i := by
  simp [clauseFinished,h63,h67]

theorem indicator_register_frame (a : Factor.Data) (rr : Fin 8 → Bool) (hash result : List Bool)
    (i : Fin 40) (hi : 8 ≤ i.val) :
    (indicatorFinished a rr hash result).regs i=a.regs i := by
  have hout : ¬∃j,Factor.nativeRegisters j=i := by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    omega
  change Function.extend Factor.nativeRegisters rr (readied a).regs i=_
  rw [Function.extend_apply' _ _ _ hout]
  have h0 : i≠0 := by intro h; subst i; simp at hi
  have h1 : i≠1 := by intro h; subst i; simp at hi
  have h2 : i≠2 := by intro h; subst i; simp at hi
  simp [readied,h0,h1,h2]

theorem clause_register_frame (a : Factor.Data) (rr : Fin 8 → Bool) (result : List Bool)
    (i : Fin 40) (hi : 8 ≤ i.val) :
    (clauseFinished a rr result).regs i=a.regs i := by
  apply Function.extend_apply'
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  omega

@[simp] theorem indicator_theta (a : Factor.Data) (rr : Fin 8 → Bool) (hash result : List Bool) :
    (indicatorFinished a rr hash result).stacks 78=a.stacks 78 :=
  indicator_frame a rr hash result 78 (by decide) (by decide) (by decide)

@[simp] theorem indicator_index (a : Factor.Data) (rr : Fin 8 → Bool) (hash result : List Bool) :
    (indicatorFinished a rr hash result).stacks 307=a.stacks 307 :=
  indicator_frame a rr hash result 307 (by decide) (by decide) (by decide)

end SubexponentialSAT.SqrtLog.LeafProgram.FactorServices

end OAI.Algorithms
