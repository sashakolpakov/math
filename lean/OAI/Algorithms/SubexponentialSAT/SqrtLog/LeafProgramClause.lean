import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramInterpreter

namespace OAI.Algorithms

/-! Evaluate the optional marked clause without applying a hash idempotent.
The constant seed is copied by the machine, and every original literal is
processed by the same concrete decoder and sparse arithmetic as hash rows. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Clause

open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open MomentsProgram

abbrev command : Cmd 8 96 := .seq (copy 69 67 70) (clauseLoop arithmetic)
def program := compiled command 63 67

theorem command_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : List (Product.Entry n (baseWidth p t) d))
    (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
    (degree width : List Bool) (u J : ℕ)
    (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (entries : List (List Bool × List Bool))
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val)=some (Product.bytes (incidence v)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ht : high 6=Squarefree.Program.lookupRecords entries)
    (ho : high 13=Product.bytes one) (hm : high 20=RingProgram.flat minus)
    (htmp : high 14=[])
    (ls : List (SAT.Literal (Fin n))) :
    let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table)
      degree (List.replicate u true) (List.replicate J true)
    let update := HashCircuitProgram.Native.Clause.step p t M cache table minus one incidence u J
    ∃ k rr, k ≤ 7*(Product.bytes one).length+8+
        DynamicFold.work HashCircuitProgram.Native.Clause.literalBits update
          (HashCircuitProgram.Native.Clause.cost p t M cache table minus one incidence degree u J entries)
          ls one ∧
      Eval command k
        (Memory.state regs (Product.tapes e)
          (HashCircuitProgram.Native.Clause.recordHigh high []
            (Encoding.encodeList id (ls.map HashCircuitProgram.Native.Clause.literalBits)) []))
        (RecordPrograms.state literalPorts
          (HashCircuitProgram.Native.Clause.base rr e high (Product.bytes (DynamicFold.value update ls one)))
          false true false [] []) := by
  dsimp only
  let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table)
    degree (List.replicate u true) (List.replicate J true)
  let source := Encoding.encodeList id (ls.map HashCircuitProgram.Native.Clause.literalBits)
  let h0 := HashCircuitProgram.Native.Clause.recordHigh high [] source []
  let h1 := Function.update h0 (11 : Fin 40) (Product.bytes one)
  let r1 := readRegs regs 0 1 none
  have hc := Memory.copy_high_high regs (Product.tapes e) h0 13 11 14
    (by decide) (by decide) (by decide)
    (by
      change high 14 = []
      exact htmp)
  have h13 : h0 13=Product.bytes one := by
    change high 13 = Product.bytes one
    exact ho
  have h11 : h0 11=[] := by
    simp [h0,HashCircuitProgram.Native.Clause.recordHigh,HashCircuitProgram.Native.Clause.baseHigh]
  simp only [h13,h11,List.append_nil] at hc
  obtain ⟨k,hk,rr,he⟩ := HashCircuitProgram.Native.Clause.command_eval p t M cache table minus one
    incidence degree u J entries hz width hd hw hl r1 high ht ho hm htmp ls one []
      (r1 0) (r1 1) (r1 2)
  have hi : RecordPrograms.state literalPorts
      (HashCircuitProgram.Native.Clause.base r1 e high (Product.bytes one))
      (r1 0) (r1 1) (r1 2) (source++[]) [] =
        Memory.state r1 (Product.tapes e) h1 := by
    rw [HashCircuitProgram.Native.Clause.record_state]
    apply congrArg₂ StructuredProgram.State.mk
    · simp
    · apply congrArg (Memory.tapes (Product.tapes e))
      funext i
      fin_cases i <;> simp [h1,h0,HashCircuitProgram.Native.Clause.recordHigh,
        HashCircuitProgram.Native.Clause.baseHigh,literalHigh]
  rw [hi] at he
  refine ⟨7*(Product.bytes one).length+5+k,rr,by omega,?_⟩
  exact hc.seq he

def callerRegisters (i : Fin 8) : Fin 40 := i.castAdd 32
def callerStacks (i : Fin 96) : Fin 768 := i.castAdd 672
abbrev caller : Cmd 40 768 :=
  .call (ProgramLinking.liftProgram program callerRegisters callerStacks)

end SubexponentialSAT.SqrtLog.LeafProgram.Clause

end OAI.Algorithms
