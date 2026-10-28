import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramArithmeticNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramRecords

namespace OAI.Algorithms

/-! A native fold of computed sparse factors. The input records contain actual
serialized sparse dictionaries. Each iteration parses one dictionary, invokes
the checked sparse product table, and reclaims the temporary operand. This is
the multiplication stage shared by hash indicators and the marked clause. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Product

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram.Native

def ports : RecordPrograms.Ports 8 96 :=
  ⟨0,1,2,71,72,by decide,by decide,by decide,by decide⟩

abbrev callback : Cmd 8 96 :=
  .seq (transfer 72 61) (.seq (productAdapter product) recordReturn)

abbrev command : Cmd 8 96 := RecordPrograms.iterate ports callback
def program := compiled command 71 67

def baseHigh (high : Fin 40 → List Bool) (acc : List Bool) : Fin 40 → List Bool :=
  Function.update (Function.update high 5 []) 11 acc

def base (regs : Fin 8 → Bool) (e : MomentsProgram.Product.Store)
    (high : Fin 40 → List Bool) (acc : List Bool) : Machine :=
  Memory.state regs (MomentsProgram.Product.tapes e) (baseHigh high acc)

def recordHigh (high : Fin 40 → List Bool) (acc src payload : List Bool) : Fin 40 → List Bool :=
  Function.update (Function.update (baseHigh high acc) 15 src) 16 payload

theorem record_state (regs : Fin 8 → Bool) (e : MomentsProgram.Product.Store)
    (high : Fin 40 → List Bool) (acc src payload : List Bool) (v pr f : Bool) :
    RecordPrograms.state ports (base regs e high acc) v pr f src payload =
      Memory.state (Function.update (Function.update (Function.update regs 0 v) 1 pr) 2 f)
        (MomentsProgram.Product.tapes e) (recordHigh high acc src payload) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · change Function.update (Function.update
        (Memory.tapes (MomentsProgram.Product.tapes e) (baseHigh high acc))
        (Memory.highPort 15) src) (Memory.highPort 16) payload =
      Memory.tapes (MomentsProgram.Product.tapes e) (recordHigh high acc src payload)
    rw [Memory.update_high,Memory.update_high]
    rfl

def stepBudget (left right result : List Bool) (nativeWork : ℕ) : ℕ :=
  9*left.length + 14*right.length + 9*result.length + nativeWork + 35

/-- The product callback has no abstract operation premise: its arithmetic
execution is obtained directly from the concrete sparse product program. -/
theorem callback_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (left right : List (MomentsProgram.Product.Entry n (baseWidth p t) d))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool) (tail : List Bool)
    (htmp : high 14 = []) :
    let e := MomentsProgram.Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table)
      degree (List.replicate u true) (List.replicate J true)
    let result := MomentsProgram.Product.run p t M cache table u J left right []
    ∃ cost ≤ stepBudget (MomentsProgram.Product.bytes left) (MomentsProgram.Product.bytes right)
        (MomentsProgram.Product.bytes result) (MomentsProgram.Product.work p t M cache table u J left right []),
      ∃ rr, Eval callback cost
        (RecordPrograms.state ports (base regs e high (MomentsProgram.Product.bytes left))
          false true false tail (MomentsProgram.Product.bytes right).reverse)
        (RecordPrograms.state ports (base rr e high (MomentsProgram.Product.bytes result))
          false true false tail []) := by
  dsimp only
  let e := MomentsProgram.Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table)
    degree (List.replicate u true) (List.replicate J true)
  let a := MomentsProgram.Product.bytes left
  let b := MomentsProgram.Product.bytes right
  let result := MomentsProgram.Product.bytes (MomentsProgram.Product.run p t M cache table u J left right [])
  let r0 := Function.update (Function.update (Function.update regs 0 false) 1 true) 2 false
  let h0 := recordHigh high a tail b.reverse
  let h1 := Function.update (recordHigh high a tail []) 5 b
  have hm := transfer_eval (Memory.state r0 (MomentsProgram.Product.tapes e) h0)
    (Memory.highPort 16) (Memory.highPort 5) (by decide)
  have htransfer : transferred (Memory.state r0 (MomentsProgram.Product.tapes e) h0)
      (Memory.highPort 16) (Memory.highPort 5) =
      Memory.state (readRegs r0 0 1 none) (MomentsProgram.Product.tapes e) h1 := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · change Function.update (Function.update
        (Memory.tapes (MomentsProgram.Product.tapes e) h0) (Memory.highPort 16) [])
        (Memory.highPort 5) ((Memory.tapes (MomentsProgram.Product.tapes e) h0
          (Memory.highPort 16)).reverse ++
          Memory.tapes (MomentsProgram.Product.tapes e) h0 (Memory.highPort 5)) =
        Memory.tapes (MomentsProgram.Product.tapes e) h1
      rw [Memory.tapes_high,Memory.tapes_high,Memory.update_high,Memory.update_high]
      apply congrArg (Memory.tapes (MomentsProgram.Product.tapes e))
      funext i
      fin_cases i <;> simp [h0,h1,recordHigh,baseHigh]
  have hm' : Eval (transfer 72 61) (3*b.length+3)
      (Memory.state r0 (MomentsProgram.Product.tapes e) h0)
      (Memory.state (readRegs r0 0 1 none) (MomentsProgram.Product.tapes e) h1) := by
    rw [htransfer] at hm
    have hlen : (Memory.tapes (MomentsProgram.Product.tapes e) h0 72).length = b.length := by
      rw [show (72 : Fin 96) = Memory.highPort 16 by decide, Memory.tapes_high]
      simp [h0,recordHigh,baseHigh]
    rw [show Memory.highPort 16 = (72 : Fin 96) by decide,
      show Memory.highPort 5 = (61 : Fin 96) by decide] at hm
    change Eval (transfer 72 61) (3 * (Memory.tapes
      (MomentsProgram.Product.tapes e) h0 72).length + 3) _ _ at hm
    rw [hlen] at hm
    simpa only [Memory.state,Memory.tapes_high,h0,recordHigh,
      Function.update_same,List.length_reverse] using hm
  obtain ⟨k,hk,rr,hp⟩ := ProductCallback.eval p t M cache hz table degree width hd hw u J left right
    (readRegs r0 0 1 none) h1 (by simp [h1,recordHigh,baseHigh,a]) (by simp [h1,b])
    (by simpa [h1,recordHigh,baseHigh] using htmp)
  have hh : ProductCallback.resultHigh h1 result = recordHigh high result tail [] := by
    funext i; fin_cases i <;> simp [ProductCallback.resultHigh,h1,recordHigh,baseHigh]
  rw [hh] at hp
  have hr := recordReturn_eval (Memory.state rr (MomentsProgram.Product.tapes e) (recordHigh high result tail []))
  refine ⟨3*b.length+3+k+3,?_,rr,?_⟩
  · dsimp [stepBudget,a,b,result] at *
    omega
  · rw [record_state,record_state]
    exact hm'.seq (hp.seq hr)

end SubexponentialSAT.SqrtLog.LeafProgram.Product

end OAI.Algorithms
