import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafMarkedProgramWide

namespace OAI.Algorithms

/-! The collector needs numerical correctness and a length bound, not canonical
binary output from each full branch aggregation. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Marked.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms

def QueryValueContract (query : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 763 → List Bool) → Prop) (valid : List Bool → Prop) : Prop :=
  ∀ bits tail (base : Data), valid bits → invariant ready base →
    ∃ n middle, n ≤ queryCost bits ∧ ready (workspace middle) ∧
      read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
      (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
      Eval query n (state recordPorts base false true false tail bits.reverse)
        (state recordPorts middle false true false tail [])

theorem value_callback (query : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 763 → List Bool) → Prop) (valid : List Bool → Prop)
    (hq : QueryValueContract query count queryCost width ready valid)
    (bits tail : List Bool) (base : Data) (hv : valid bits) (hb : invariant ready base) :
    ∃ n next, n ≤ queryCost bits + 16*(max (read base).length (width bits)+1)+3 ∧
      invariant ready next ∧
      BinaryArithmetic.toNat (read next) = BinaryArithmetic.toNat (read base)+count bits ∧
      (read next).length ≤ (read base).length + width bits + 1 ∧
      Eval (callback query) n (state recordPorts base false true false tail bits.reverse)
        (state recordPorts next false true false tail []) := by
  obtain ⟨n,middle,hn,hm,hr,hv,hl,hs,ht⟩ := hq bits tail base hv hb
  obtain ⟨m,next,hmn,hi,ha,he⟩ :=
    add_count_eval ready middle tail (read base) (middle.stacks 323) hm hr rfl hs
  refine ⟨n+m,next,by omega,hi,?_,?_,ht.seq he⟩
  · rw [ha,BinaryArithmetic.toNat_add,hv]
  · rw [ha]
    have := BinaryArithmetic.length_add (read base) (middle.stacks 323)
    omega

def valueInputSize (width : List Bool → ℕ) (records : List (List Bool)) : ℕ :=
  (records.map fun bits => bits.length + width bits + 1).sum

def valueBudget (queryCost width : List Bool → ℕ) (records : List (List Bool))
    (acc : List Bool) : ℕ :=
  4+(records.map queryCost).sum + records.length*(22*(acc.length+valueInputSize width records)+26)

theorem value_loop_run (query : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 763 → List Bool) → Prop) (valid : List Bool → Prop)
    (hq : QueryValueContract query count queryCost width ready valid)
    (records : List (List Bool)) (suffix : List Bool) (base : Data) (M : ℕ)
    (hrecords : ∀ bits ∈ records, valid bits) (hb : invariant ready base)
    (hsize : (read base).length + valueInputSize width records ≤ M) :
    ∃ n next, n ≤ 1+(records.map queryCost).sum + records.length*(22*M+26) ∧
      invariant ready next ∧
      BinaryArithmetic.toNat (read next) = BinaryArithmetic.toNat (read base)+(records.map count).sum ∧
      Eval (loop recordPorts (callback query)) n (afterTag recordPorts base records suffix)
        (state recordPorts next false true false suffix []) := by
  induction records generalizing base with
  | nil =>
      refine ⟨1,base,by simp,hb,by simp,?_⟩
      apply Eval.while_false
      simp [afterTag]
  | cons bits rest ih =>
      let tail := Encoding.encodeList id rest ++ suffix
      obtain ⟨n,middle,hn,hm,hvalue,hlen,hcall⟩ :=
        value_callback query count queryCost width ready valid hq bits tail base
          (hrecords bits (by simp)) hb
      have hs : (read base).length+bits.length+width bits+1+valueInputSize width rest ≤ M := by
        simpa [valueInputSize,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hsize
      have hrsize : (read middle).length + valueInputSize width rest ≤ M := by omega
      obtain ⟨m,next,hmn,hi,hv,ht⟩ :=
        ih middle (fun b hh => hrecords b (by simp [hh])) hm hrsize
      have hreader : Eval (reader recordPorts) (6*bits.length+4)
          (afterTag recordPorts base (bits::rest) suffix)
          (state recordPorts base false true false tail bits.reverse) := by
        simpa [afterTag,tail] using reader_eval recordPorts base bits tail [] true true false
      have hpop : Eval
          (.ite recordPorts.found (atom (.set recordPorts.tag false))
            (atom (.pop recordPorts.source recordPorts.tag recordPorts.present))) 2
          (state recordPorts middle false true false tail [])
          (afterTag recordPorts middle rest suffix) := by
        apply Eval.ite_false (by simp)
        exact pop_list_eval recordPorts middle rest suffix false true
      refine ⟨(6*bits.length+4+(n+2))+m+1,next,?_,hi,?_,?_⟩
      · have hc : n ≤ queryCost bits + 16*(M+1)+3 := by omega
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        nlinarith
      · rw [hv,hvalue]
        simp only [List.map_cons,List.sum_cons]
        omega
      · exact Eval.while_true (by simp [afterTag])
          (hreader.seq (hcall.seq hpop)) ht

theorem value_program_run (query : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 763 → List Bool) → Prop) (valid : List Bool → Prop)
    (hq : QueryValueContract query count queryCost width ready valid)
    (records : List (List Bool)) (suffix : List Bool) (base : Data)
    (hrecords : ∀ bits ∈ records, valid bits) (hb : invariant ready base) (v pr f : Bool) :
    ∃ next, invariant ready next ∧
      BinaryArithmetic.toNat (read next) = BinaryArithmetic.toNat (read base)+(records.map count).sum ∧
      RunsIn (program query) (valueBudget queryCost width records (read base))
        ((state recordPorts base v pr f (Encoding.encodeList id records++suffix) []).withPC
          (some (program query).entry))
        ((state recordPorts next false true false suffix []).withPC none) := by
  obtain ⟨n,next,hn,hi,hv,ht⟩ := value_loop_run query count queryCost width ready valid hq
    records suffix base ((read base).length+valueInputSize width records) hrecords hb le_rfl
  have hrun := (set_found_eval recordPorts base v pr f false _ []).seq
    ((pop_list_eval recordPorts base records suffix v pr).seq ht)
  refine ⟨next,hi,hv,1+(1+n)+1,?_,compiled_halt_trace hrun 320 322⟩
  dsimp [valueBudget]
  omega
end SubexponentialSAT.SqrtLog.LeafProgram.Marked.Wide

end OAI.Algorithms
