import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramProduct

namespace OAI.Algorithms

/-! Complete typed run of the fixed native factor fold. The recursion below
describes the output and the paid trace length; it is not used by the program. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Product

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ) :
    List (MomentsProgram.Product.Entry n (baseWidth p t) d) →
    List (List (MomentsProgram.Product.Entry n (baseWidth p t) d)) →
    List (MomentsProgram.Product.Entry n (baseWidth p t) d)
  | seed, [] => seed
  | seed, x::xs => run p t M cache table u J
      (MomentsProgram.Product.run p t M cache table u J seed x []) xs

def work (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ) :
    List (MomentsProgram.Product.Entry n (baseWidth p t) d) →
    List (List (MomentsProgram.Product.Entry n (baseWidth p t) d)) → ℕ
  | _, [] => 0
  | seed, x::xs =>
      let next := MomentsProgram.Product.run p t M cache table u J seed x []
      6*(MomentsProgram.Product.bytes x).length +
        stepBudget (MomentsProgram.Product.bytes seed) (MomentsProgram.Product.bytes x)
          (MomentsProgram.Product.bytes next) (MomentsProgram.Product.work p t M cache table u J seed x []) + 7 +
        work p t M cache table u J next xs

theorem loop_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (seed : List (MomentsProgram.Product.Entry n (baseWidth p t) d))
    (xs : List (List (MomentsProgram.Product.Entry n (baseWidth p t) d)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool) (suffix : List Bool)
    (htmp : high 14 = []) :
    let e := MomentsProgram.Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table)
      degree (List.replicate u true) (List.replicate J true)
    ∃ cost ≤ 1 + work p t M cache table u J seed xs, ∃ rr,
      Eval (RecordPrograms.loop ports callback) cost
        (afterTag ports (base regs e high (MomentsProgram.Product.bytes seed))
          (xs.map MomentsProgram.Product.bytes) suffix)
        (RecordPrograms.state ports
          (base rr e high (MomentsProgram.Product.bytes (run p t M cache table u J seed xs)))
          false true false suffix []) := by
  dsimp only
  let e := MomentsProgram.Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table)
    degree (List.replicate u true) (List.replicate J true)
  induction xs generalizing seed regs with
  | nil =>
      refine ⟨1,by simp [work],regs,?_⟩
      apply Eval.while_false
      simp [afterTag,ports,RecordPrograms.state]
  | cons x xs ih =>
      let next := MomentsProgram.Product.run p t M cache table u J seed x []
      let tail := Encoding.encodeList id (xs.map MomentsProgram.Product.bytes) ++ suffix
      obtain ⟨k,hk,r1,hc⟩ := callback_eval p t M cache hz table degree width hd hw u J seed x regs high tail htmp
      have hr : Eval (reader ports) (6*(MomentsProgram.Product.bytes x).length+4)
          (afterTag ports (base regs e high (MomentsProgram.Product.bytes seed))
            ((x::xs).map MomentsProgram.Product.bytes) suffix)
          (RecordPrograms.state ports (base regs e high (MomentsProgram.Product.bytes seed))
            false true false tail (MomentsProgram.Product.bytes x).reverse) := by
        simpa [afterTag,tail] using reader_eval ports
          (base regs e high (MomentsProgram.Product.bytes seed))
          (MomentsProgram.Product.bytes x) tail [] true true false
      have hb : Eval (.ite ports.found (atom (.set ports.tag false))
          (atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports (base r1 e high (MomentsProgram.Product.bytes next))
            false true false tail [])
          (afterTag ports (base r1 e high (MomentsProgram.Product.bytes next))
            (xs.map MomentsProgram.Product.bytes) suffix) := by
        apply Eval.ite_false (by simp)
        exact pop_list_eval ports _ _ suffix false true
      obtain ⟨j,hj,rr,hl⟩ := ih next r1
      refine ⟨(6*(MomentsProgram.Product.bytes x).length+4+(k+2))+j+1,?_,rr,?_⟩
      · simp only [work]
        dsimp only [next] at *
        omega
      · exact Eval.while_true (by simp [afterTag]) (hr.seq (hc.seq hb)) hl

theorem command_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (seed : List (MomentsProgram.Product.Entry n (baseWidth p t) d))
    (xs : List (List (MomentsProgram.Product.Entry n (baseWidth p t) d)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool) (suffix : List Bool)
    (htmp : high 14 = []) (v pr f : Bool) :
    let e := MomentsProgram.Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table)
      degree (List.replicate u true) (List.replicate J true)
    ∃ cost ≤ 3 + work p t M cache table u J seed xs, ∃ rr,
      Eval command cost
        (RecordPrograms.state ports (base regs e high (MomentsProgram.Product.bytes seed)) v pr f
          (Encoding.encodeList id (xs.map MomentsProgram.Product.bytes) ++ suffix) [])
        (RecordPrograms.state ports
          (base rr e high (MomentsProgram.Product.bytes (run p t M cache table u J seed xs)))
          false true false suffix []) := by
  dsimp only
  obtain ⟨k,hk,rr,he⟩ := loop_eval p t M cache hz table degree width hd hw u J seed xs regs high suffix htmp
  exact ⟨1+(1+k),by omega,rr,
    (set_found_eval ports _ v pr f false _ []).seq ((pop_list_eval ports _ _ suffix v pr).seq he)⟩

theorem program_run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (seed : List (MomentsProgram.Product.Entry n (baseWidth p t) d))
    (xs : List (List (MomentsProgram.Product.Entry n (baseWidth p t) d)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool) (suffix : List Bool)
    (htmp : high 14 = []) (v pr f : Bool) :
    let e := MomentsProgram.Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table)
      degree (List.replicate u true) (List.replicate J true)
    ∃ rr, RunsIn program (4 + work p t M cache table u J seed xs)
        ((RecordPrograms.state ports (base regs e high (MomentsProgram.Product.bytes seed)) v pr f
          (Encoding.encodeList id (xs.map MomentsProgram.Product.bytes) ++ suffix) []).withPC (some program.entry))
        ((RecordPrograms.state ports
          (base rr e high (MomentsProgram.Product.bytes (run p t M cache table u J seed xs)))
          false true false suffix []).withPC none) := by
  dsimp only
  obtain ⟨k,hk,rr,he⟩ := command_eval p t M cache hz table degree width hd hw u J seed xs regs high suffix htmp v pr f
  exact ⟨rr,k+1,by omega,compiled_halt_trace he 71 67⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Product

end OAI.Algorithms
