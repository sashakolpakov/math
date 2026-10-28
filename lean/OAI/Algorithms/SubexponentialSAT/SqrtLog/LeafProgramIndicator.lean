import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramInterpreter
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramFinal

namespace OAI.Algorithms

/-! A closed native sparse-hash indicator service. It first interprets the
actual inline weighted-clause row and then applies the computed idempotent
coefficient tape. The resulting indicator is never supplied as input. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Indicator

attribute [local simp] Fin.addCases

open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps
open MomentsProgram

noncomputable abbrev command : Cmd 8 96 :=
  .seq (.call HashCircuitProgram.Native.program) IdempotentApplyProgram.command

noncomputable def program := compiled command 64 67

def rawHash {p t n d : ℕ} [Fact p.Prime] (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (ws : List (Row.WeightedClause n (baseWidth p t) d)) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  DynamicFold.value (Row.value p t ctx.modulus ctx.cache ctx.table minus one incidence ctx.u ctx.J) ws []

def result {p t n d : ℕ} [Fact p.Prime] (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t))) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  IdempotentApplyProgram.applied ctx minus (rawHash ctx minus one incidence ws) one digits

theorem record_apply_ready (high : Fin 40 → List Bool) (hash : List Bool)
    (hready : IdempotentApplyProgram.Multiplier.ready high) :
    IdempotentApplyProgram.Multiplier.ready (Row.recordHigh high hash [] []) := by
  intro i hi
  have h := hready i hi
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    first | rfl | simpa [Row.recordHigh,Row.baseHigh,Clause.baseHigh,literalHigh] using h

/-- Both constituent executions are derived from their concrete native
programs. All dimensions, clauses, and coefficients remain runtime data. -/
theorem command_eval {p t n d : ℕ} [Fact p.Prime] (ctx : Context p t n d)
    (hd : 0 < d) (hB : 0 < baseWidth p t)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool))
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ht : high 6 = Squarefree.Program.lookupRecords entries)
    (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minus)
    (htape : high 22 = IdempotentApplyProgram.triplesTape digits)
    (h23 : high 23 = []) (hshape : (high 32).length = n)
    (hready : IdempotentApplyProgram.Multiplier.ready high) :
    let e := Product.idle ctx.modulus.bits ctx.width ctx.cache.zero.val
      (RingTriple.tableEncoding ctx.table) (List.replicate d true)
      (List.replicate ctx.u true) (List.replicate ctx.J true)
    ∃ k rr, k ≤ 7 + DynamicFold.work Row.payload
        (Row.value p t ctx.modulus ctx.cache ctx.table minus one incidence ctx.u ctx.J)
        (Row.cost p t ctx.modulus ctx.cache ctx.table minus one incidence
          (List.replicate d true) ctx.u ctx.J entries) ws [] +
        IdempotentApplyProgram.applicationBudget ctx minus (rawHash ctx minus one incidence ws) one digits ∧
      Eval command k
        (RecordPrograms.state rowPorts (Row.base regs e high []) false true false
          (Encoding.encodeList id (ws.map Row.payload)) [])
        (Memory.state rr (low ctx) (Function.update
          (Row.recordHigh high (Product.bytes (rawHash ctx minus one incidence ws)) [] [])
          11 (Product.bytes (result ctx minus one incidence ws digits)))) := by
  dsimp only
  let e := Product.idle ctx.modulus.bits ctx.width ctx.cache.zero.val
    (RingTriple.tableEncoding ctx.table) (List.replicate d true)
    (List.replicate ctx.u true) (List.replicate ctx.J true)
  let h := rawHash ctx minus one incidence ws
  have htmp : high 14 = [] := hready 14 (by simp)
  obtain ⟨r1,k1,hk1,he1⟩ := Row.program_runs p t ctx.modulus ctx.cache ctx.table minus one incidence
    (List.replicate d true) ctx.u ctx.J entries ctx.zeroBound ctx.width (by simp) ctx.widthLength
    hl regs high ht ho hm htmp ws
  have first : Eval (.call HashCircuitProgram.Native.program) k1
      (RecordPrograms.state rowPorts (Row.base regs e high []) false true false
        (Encoding.encodeList id (ws.map Row.payload)) [])
      (Memory.state (Function.update (Function.update (Function.update r1 0 false) 1 true) 2 false)
        (low ctx) (Row.recordHigh high (Product.bytes h) [] [])) := by
    have he := Eval.call HashCircuitProgram.Native.program he1
    change Eval (.call HashCircuitProgram.Native.program) k1
      (RecordPrograms.state rowPorts (Row.base regs e high []) false true false
        (Encoding.encodeList id (ws.map Row.payload)) [])
      (RecordPrograms.state rowPorts (Row.base r1 e high (Product.bytes h)) false true false [] []) at he
    rw [Row.record_state r1 e high (Product.bytes h) [] [] false true false] at he
    exact he
  let middle := Row.recordHigh high (Product.bytes h) [] []
  obtain ⟨k2,hk2,r2,he2⟩ := IdempotentApplyProgram.command_eval ctx hd hB minus h one digits
    (Function.update (Function.update (Function.update r1 0 false) 1 true) 2 false) middle
    (by simp [middle,Row.recordHigh,Row.baseHigh])
    (by simpa [middle,Row.recordHigh,Row.baseHigh,Clause.baseHigh,literalHigh] using ho)
    (by simpa [middle,Row.recordHigh,Row.baseHigh,Clause.baseHigh,literalHigh] using hm)
    (by simpa [middle,Row.recordHigh,Row.baseHigh,Clause.baseHigh,literalHigh] using htape)
    (by simpa [middle,Row.recordHigh,Row.baseHigh,Clause.baseHigh,literalHigh] using h23)
    (by simpa [middle,Row.recordHigh,Row.baseHigh,Clause.baseHigh,literalHigh] using hshape)
    (record_apply_ready high (Product.bytes h) hready)
  dsimp only [h] at hk2
  refine ⟨k1+k2,r2,by omega,?_⟩
  exact first.seq he2

/-- The node's theta remains on global78. The coefficient tape expected on
local78 is relocated to143, which is reserved by the assignment producer. -/
def callerRegisters (i : Fin 8) : Fin 16 := i.castAdd 8

def callerStacks (i : Fin 96) : Fin 256 :=
  Equiv.swap 78 143 (i.castAdd 160)

theorem callerRegisters_injective : Function.Injective callerRegisters :=
  Fin.castAdd_injective 8 8

theorem callerStacks_injective : Function.Injective callerStacks :=
  (Equiv.swap 78 143).injective.comp (Fin.castAdd_injective 96 160)

noncomputable abbrev caller : Cmd 16 256 :=
  .call (ProgramLinking.liftProgram program callerRegisters callerStacks)

@[simp] theorem coefficient_port : callerStacks 78 = 143 := by decide
@[simp] theorem result_port : callerStacks 67 = 67 := by decide

theorem node_frame (frame : State 16 256) (a : State 8 96) :
    (embedState callerRegisters callerStacks frame a).stacks 78 = frame.stacks 78 := by
  apply embedState_stack_frame
  rintro ⟨i, hi⟩
  change Equiv.swap 78 143 (i.castAdd 160) = 78 at hi
  rw [Equiv.swap_apply_eq_iff] at hi
  have hv := congrArg Fin.val hi
  simp at hv
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.Indicator

end OAI.Algorithms
