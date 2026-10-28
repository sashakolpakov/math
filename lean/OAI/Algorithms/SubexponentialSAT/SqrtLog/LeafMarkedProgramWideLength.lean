import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafMarkedProgramWideValueCorrect

namespace OAI.Algorithms

/-! Explicit output-length accounting for final mass normalization. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Marked.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms

def outputGrowth (width : List Bool → ℕ) (records : List (List Bool)) : ℕ :=
  (records.map fun bits => width bits+1).sum

theorem value_loop_run_length (query : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 763 → List Bool) → Prop) (valid : List Bool → Prop)
    (hq : QueryValueContract query count queryCost width ready valid)
    (records : List (List Bool)) (suffix : List Bool) (base : Data) (M : ℕ)
    (hrecords : ∀ bits ∈ records, valid bits) (hb : invariant ready base)
    (hsize : (read base).length + valueInputSize width records ≤ M) :
    ∃ n next, n ≤ 1+(records.map queryCost).sum + records.length*(22*M+26) ∧
      invariant ready next ∧
      BinaryArithmetic.toNat (read next) = BinaryArithmetic.toNat (read base)+(records.map count).sum ∧
      (read next).length ≤ (read base).length+outputGrowth width records ∧
      Eval (loop recordPorts (callback query)) n (afterTag recordPorts base records suffix)
        (state recordPorts next false true false suffix []) := by
  induction records generalizing base with
  | nil =>
      refine ⟨1,base,by simp,hb,by simp,by simp [outputGrowth],?_⟩
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
      obtain ⟨m,next,hmn,hi,hv,hfinal,ht⟩ :=
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
      refine ⟨(6*bits.length+4+(n+2))+m+1,next,?_,hi,?_,?_,?_⟩
      · have hc : n ≤ queryCost bits + 16*(M+1)+3 := by omega
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        nlinarith
      · rw [hv,hvalue]
        simp only [List.map_cons,List.sum_cons]
        omega
      · simp only [outputGrowth,List.map_cons,List.sum_cons] at hfinal ⊢
        omega
      · exact Eval.while_true (by simp [afterTag])
          (hreader.seq (hcall.seq hpop)) ht

theorem value_program_run_length (query : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 763 → List Bool) → Prop) (valid : List Bool → Prop)
    (hq : QueryValueContract query count queryCost width ready valid)
    (records : List (List Bool)) (suffix : List Bool) (base : Data)
    (hrecords : ∀ bits ∈ records, valid bits) (hb : invariant ready base) (v pr f : Bool) :
    ∃ next, invariant ready next ∧
      BinaryArithmetic.toNat (read next) = BinaryArithmetic.toNat (read base)+(records.map count).sum ∧
      (read next).length ≤ (read base).length+outputGrowth width records ∧
      RunsIn (program query) (valueBudget queryCost width records (read base))
        ((state recordPorts base v pr f (Encoding.encodeList id records++suffix) []).withPC
          (some (program query).entry))
        ((state recordPorts next false true false suffix []).withPC none) := by
  obtain ⟨n,next,hn,hi,hv,hfinal,ht⟩ := value_loop_run_length query count queryCost width ready valid hq
    records suffix base ((read base).length+valueInputSize width records) hrecords hb le_rfl
  have hrun := (set_found_eval recordPorts base v pr f false _ []).seq
    ((pop_list_eval recordPorts base records suffix v pr).seq ht)
  refine ⟨next,hi,hv,hfinal,1+(1+n)+1,?_,compiled_halt_trace hrun 320 322⟩
  dsimp [valueBudget]
  omega
theorem outputGrowth_le (width : List Bool → ℕ) (records : List (List Bool))
    (W : ℕ) (hW : ∀ bits ∈ records, width bits ≤ W) :
    outputGrowth width records ≤ records.length*(W+1) := by
  induction records with
  | nil => simp [outputGrowth]
  | cons bits rest ih =>
      have hw := hW bits (by simp)
      have hr := ih (fun b hb => hW b (by simp [hb]))
      simp only [outputGrowth,List.map_cons,List.sum_cons,List.length_cons] at *
      nlinarith

variable {X Row : Type*} [Fintype X] {m : ℕ}

theorem value_program_marked_length (query : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 763 → List Bool) → Prop) (valid : List Bool → Prop)
    (hq : QueryValueContract query count queryCost width ready valid)
    (rowAccept : Row → X → Bool) (rows : List Row) (bad : Fin m → X → Bool)
    (reference : Fin m → List Bool) (hvalid : ∀ e, valid (reference e))
    (hcount : ∀ e, count (reference e) = markedCount rowAccept rows bad e)
    (W : ℕ) (hwidth : ∀ e, width (reference e) ≤ W)
    (suffix : List Bool) (base : Data) (hb : invariant ready base) (hzero : read base = [])
    (v pr f : Bool) :
    ∃ next, invariant ready next ∧
      BinaryArithmetic.toNat (read next) = HashSelect.mass rowAccept (violationWeight bad) rows ∧
      (read next).length ≤ m*(W+1) ∧
      RunsIn (program query) (valueBudget queryCost width (List.ofFn reference) [])
        ((state recordPorts base v pr f
          (Encoding.encodeList id (List.ofFn reference)++suffix) []).withPC (some (program query).entry))
        ((state recordPorts next false true false suffix []).withPC none) := by
  obtain ⟨next,hi,hv,hl,ht⟩ := value_program_run_length query count queryCost width ready valid hq
    (List.ofFn reference) suffix base (by
      intro bits hh
      obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hh
      exact hvalid e) hb v pr f
  have hbound := outputGrowth_le width (List.ofFn reference) W (by
    intro bits hh
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hh
    exact hwidth e)
  refine ⟨next,hi,?_,?_,by simpa [hzero] using ht⟩
  · rw [hv,hzero]
    simp only [BinaryArithmetic.toNat,zero_add,List.map_ofFn,Function.comp_def,List.sum_ofFn]
    simp_rw [hcount]
    exact sum_markedCount rowAccept rows bad
  · simpa [hzero] using hl.trans (Nat.add_le_add_left hbound (read base).length)
end SubexponentialSAT.SqrtLog.LeafProgram.Marked.Wide

end OAI.Algorithms
