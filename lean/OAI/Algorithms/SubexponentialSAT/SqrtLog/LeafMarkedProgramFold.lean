import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFold

namespace OAI.Algorithms

/-! The measured physical fold, restricted to explicitly valid reference records. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms
variable {r s : ℕ} {A : Type*}

abbrev DynamicFoldContractOn (ports : Ports r s) (callback : Cmd r s)
    (read : State r s → A) (step : List Bool → A → A)
    (cost : A → List Bool → ℕ) (invariant : State r s → Prop)
    (valid : List Bool → Prop) : Prop :=
  ∀ (bits tail : List Bool) (base : State r s), valid bits → invariant base →
    ∃ n next, n ≤ cost (read base) bits ∧ invariant next ∧
      read next = step bits (read base) ∧
      Eval callback n (state ports base false true false tail bits.reverse)
        (state ports next false true false tail [])

theorem dynamic_loop_run_on (ports : Ports r s) (callback : Cmd r s)
    (read : State r s → A) (step : List Bool → A → A)
    (cost : A → List Bool → ℕ) (invariant : State r s → Prop)
    (valid : List Bool → Prop)
    (contract : DynamicFoldContractOn ports callback read step cost invariant valid)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (hrecords : ∀ bits ∈ records, valid bits) (hbase : invariant base) :
    ∃ n next, n ≤ 1 + foldWork step cost (read base) records ∧ invariant next ∧
      read next = records.foldl (fun a bits => step bits a) (read base) ∧
      Eval (loop ports callback) n (afterTag ports base records suffix)
        (state ports next false true false suffix []) := by
  induction records generalizing base with
  | nil =>
      refine ⟨1, base, by simp [foldWork], hbase, rfl, ?_⟩
      apply Eval.while_false
      simp [afterTag]
  | cons bits rest ih =>
      let tail := Encoding.encodeList id rest ++ suffix
      obtain ⟨n, middle, hn, hm, heffect, hc⟩ :=
        contract bits tail base (hrecords bits (by simp)) hbase
      have hr : Eval (reader ports) (6 * bits.length + 4)
          (afterTag ports base (bits :: rest) suffix)
          (state ports base false true false tail bits.reverse) := by
        simpa [afterTag, tail] using reader_eval ports base bits tail [] true true false
      have hb : Eval
          (.ite ports.found (atom (.set ports.tag false))
            (atom (.pop ports.source ports.tag ports.present))) 2
          (state ports middle false true false tail [])
          (afterTag ports middle rest suffix) := by
        apply Eval.ite_false (by simp)
        exact pop_list_eval ports middle rest suffix false true
      obtain ⟨m, next, hmn, hi, hv, ht⟩ :=
        ih middle (fun x hx => hrecords x (by simp [hx])) hm
      refine ⟨(6 * bits.length + 4 + (n + 2)) + m + 1, next, ?_, hi, ?_, ?_⟩
      · simp only [foldWork]
        rw [heffect] at hmn
        omega
      · simpa only [List.foldl_cons, heffect] using hv
      · exact Eval.while_true (by simp [afterTag]) (Eval.seq hr (Eval.seq hc hb)) ht

theorem dynamic_fold_run_on (ports : Ports r s) (callback : Cmd r s)
    (read : State r s → A) (step : List Bool → A → A)
    (cost : A → List Bool → ℕ) (invariant : State r s → Prop)
    (valid : List Bool → Prop)
    (contract : DynamicFoldContractOn ports callback read step cost invariant valid)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (hrecords : ∀ bits ∈ records, valid bits) (hbase : invariant base) (v pr f : Bool) :
    ∃ n next, n ≤ 3 + foldWork step cost (read base) records ∧ invariant next ∧
      read next = records.foldl (fun a bits => step bits a) (read base) ∧
      Eval (foldCommand ports callback) n
        (state ports base v pr f (Encoding.encodeList id records ++ suffix) [])
        (state ports next false true false suffix []) := by
  obtain ⟨n, next, hn, hi, hv, ht⟩ :=
    dynamic_loop_run_on ports callback read step cost invariant valid contract
      records suffix base hrecords hbase
  exact ⟨1 + (1 + n), next, by omega, hi, hv,
    Eval.seq (set_found_eval ports base v pr f false _ [])
      (Eval.seq (pop_list_eval ports base records suffix v pr) ht)⟩
end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
