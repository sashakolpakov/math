import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramArithmeticNative

namespace OAI.Algorithms

/-! Native normalized addition for the persistent polynomial registers used
by the indicator Horner loop. Both operand copies and result storage are paid. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

abbrev addCore : Cmd 8 96 :=
  liftCommand Product.normalizePhase 4 42 id Memory.lowPort

abbrev add : Cmd 8 96 :=
  .seq (copy 67 4 70) (.seq (copy 61 42 70) (.seq addCore
    (.seq (clear 67) (.seq (clear 61) (.seq (copy 42 67 70) (clear 42))))))

def binaryResult (high : Fin 40 → List Bool) (result : List Bool) : Fin 40 → List Bool :=
  Function.update (Function.update (Function.update high 11 []) 5 []) 11 result

private theorem update_mapped (s : Product.Store) (w : List Bool) :
    Function.update (Product.tapes s) 4 w=Product.tapes {s with mapped:=w} := by
  funext i
  fin_cases i <;> simp [Product.tapes]

theorem add_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)
    {K : Type*} [DecidableEq K] {d : ℕ}
    (key : K → List Bool) (hk : Function.Injective key)
    (table : List Bool) (degree width uCap zCap : List Bool)
    (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ha : high 11=Normalize.bytes key source)
    (hb : high 5=Normalize.bytes key seed) (htmp : high 14=[]) :
    let e:=Product.idle M.bits width cache.zero.val table degree uCap zCap
    let result:=Normalize.bytes key (Normalize.run p t M cache source seed)
    ∃ cost ≤ 18*(Normalize.bytes key source).length+9*(Normalize.bytes key seed).length+
      9*result.length+9*degree.length+Normalize.work p t M cache key source seed+43,
      ∃ rr, Eval add cost (Memory.state regs (Product.tapes e) high)
        (Memory.state rr (Product.tapes e) (binaryResult high result)) := by
  dsimp only
  let e:=Product.idle M.bits width cache.zero.val table degree uCap zCap
  let a:=Normalize.bytes key source
  let b:=Normalize.bytes key seed
  let result:=Normalize.bytes key (Normalize.run p t M cache source seed)
  let r1:=readRegs regs 0 1 none
  let r2:=readRegs r1 0 1 none
  have h1:=Memory.copy_high_low regs (Product.tapes e) high 11 14 4 (by decide) htmp
  have he4 : Product.tapes e 4=[]:=rfl
  simp only [ha,he4,List.append_nil,update_mapped] at h1
  have h2:=Memory.copy_high_low r1 (Product.tapes {e with mapped:=a}) high 5 14 42
    (by decide) htmp
  have he42 : Product.tapes {e with mapped:=a} 42=[]:=rfl
  simp only [hb,he42,List.append_nil,Memory.update_product_acc] at h2
  obtain ⟨k,hkCost,r3,hcore⟩:=Product.normalizePhase_eval p t M cache key hk source seed r2
    {e with mapped:=a,acc:=b} rfl hw hd rfl rfl rfl rfl rfl rfl rfl rfl
  have h3:=eval_liftCommand hcore 4 42 id Memory.lowPort
    (Memory.state r2 (Product.tapes {e with mapped:=a,acc:=b}) high)
    Function.injective_id Memory.low_injective
  simp only [Product.state,Memory.embed_low] at h3
  change Eval addCore (k+1)
    (Memory.state r2 (Product.tapes {e with mapped:=a,acc:=b}) high)
    (Memory.state r3 (Product.tapes {e with acc:=result}) high) at h3
  have h4:=Memory.clear_high r3 (Product.tapes {e with acc:=result}) high 11
  simp only [ha] at h4
  let r4:=readRegs r3 0 1 none
  let high1:=Function.update high (11:Fin 40) []
  have h5:=Memory.clear_high r4 (Product.tapes {e with acc:=result}) high1 5
  have hb1 : high1 5=b:=by simpa [high1,b] using hb
  simp only [hb1] at h5
  let r5:=readRegs r4 0 1 none
  let high2:=Function.update high1 (5:Fin 40) []
  have htmp2 : high2 14=[]:=by simpa [high2,high1] using htmp
  have h6:=Memory.copy_low_high r5 (Product.tapes {e with acc:=result}) high2 42 11 14
    (by decide) htmp2
  have hres : Product.tapes {e with acc:=result} 42=result:=rfl
  have hhigh2 : high2 11=[]:=by simp [high2,high1]
  simp only [hres,hhigh2,List.append_nil] at h6
  let r6:=readRegs r5 0 1 none
  let high3:=Function.update high2 (11:Fin 40) result
  have h7:=Memory.clear_low r6 (Product.tapes {e with acc:=result}) high3 42
  simp only [hres,Memory.update_product_acc] at h7
  have he:=h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))
  refine ⟨(7*a.length+5)+(7*b.length+5)+(k+1)+(2*a.length+3)+(2*b.length+3)+
    (7*result.length+5)+(2*result.length+3),?_,readRegs r6 0 1 none,?_⟩
  · dsimp [a,b,e,result,Product.idle] at hkCost ⊢
    omega
  · convert he using 1 <;> first | rfl | (dsimp [a,b,result]; omega)

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
