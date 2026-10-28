import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientSearchCallback
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientSearchInvariant

namespace OAI.Algorithms

/-! Concrete first-success scan. Its invariant is a physical stack shape;
the callback theorem supplies actual executions on all generated records. -/

namespace SubexponentialSAT.Subexp.CoefficientSearchProgram

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

open BitProgram StructuredCalls SubexpScanPrimitives MatrixWordEncoding

variable (p : ℕ) [Fact p.Prime]

theorem callback_contract (A R : ℕ) (alphabet : List Bool) :
    RecordPrograms.CallbackContractWithOn ports callback
      (CoefficientSearchSemantics.test p A R) (fun _ => callbackBudget A R (width p))
      (Invariant p A R alphabet) (fun bits _ next => next.stacks 21 = bits)
      (fun bits => bits ∈ CoefficientSearchSemantics.rows p R) := by
  intro bits tail base hbits hbase
  obtain ⟨v,rfl⟩ := (CoefficientSearchSemantics.mem_rows p R bits).mp hbits
  rcases hbase with ⟨regs,g,neg,ok,tag,present,found,selected,source,payload,rfl,hlen⟩
  have hstart : RecordPrograms.state ports
      (wide (blank p R regs g neg ok) tag present found selected source payload
        alphabet (List.replicate A true)) false true false tail
          (CoefficientSearchSemantics.encode p v).reverse =
      wide (blank p R regs g neg ok) false true false selected tail
        (CoefficientSearchSemantics.encode p v).reverse alphabet (List.replicate A true) := by
    apply state_ext
    · funext j
      fin_cases j <;> simp [RecordPrograms.state,ports,wide]
    · funext j
      fin_cases j <;> simp [RecordPrograms.state,ports,wide]
  obtain ⟨n,hn,r,he⟩ := callback_eval p A R v regs g neg ok selected tail alphabet hlen
  let answer := CoefficientSearchSemantics.valueTest p A v
  let parity := CoefficientCheckerSemantics.advanceParity R
    (CoefficientCheckerSemantics.advanceParity A false)
  let next := wide (blank p R r false parity answer) false true answer
    (CoefficientSearchSemantics.encode p v) tail [] alphabet (List.replicate A true)
  have hnext : Invariant p A R alphabet next := by
    refine ⟨r,false,parity,answer,false,true,answer,
      CoefficientSearchSemantics.encode p v,tail,[],rfl,?_⟩
    exact (CoefficientSearchSemantics.encode_length p v).le
  have hout : next.stacks 21 = CoefficientSearchSemantics.encode p v := rfl
  have hfinish : RecordPrograms.state ports next false true
      (CoefficientSearchSemantics.test p A R (CoefficientSearchSemantics.encode p v))
      tail [] = next := by
    rw [CoefficientSearchSemantics.test_encode]
    apply RecordPrograms.state_eq_self <;> rfl
  refine ⟨n,next,hn,hnext,hout,?_⟩
  rw [hstart,hfinish]
  exact he

/-- The actual existing iterator stops at a satisfying encoded candidate and
retains the exact unread suffix. The existential statement is established
by the concrete field interpolation theorem. -/
theorem search_eval (A R : ℕ) (alphabet : List Bool) (h2 : (2 : ZMod p) ≠ 0)
    (base : Data) (hbase : Invariant p A R alphabet base) (tag present found : Bool)
    (suffix : List Bool) :
    ∃ (n : ℕ) (next : Data) (v : Fin R → ZMod p),
      n ≤ 3 + RecordPrograms.budget (fun _ => callbackBudget A R (width p))
        (CoefficientSearchSemantics.rows p R) ∧
      Invariant p A R alphabet next ∧
      next.stacks 21 = CoefficientSearchSemantics.encode p v ∧
      (∀ d < R, CoefficientDynamics.evaluate (List.ofFn v) (A + d) = (-1 : ZMod p)^(A + d)) ∧
      Eval search n
        (RecordPrograms.state ports base tag present found
          (ProgramEncoding.encodeRecords (CoefficientSearchSemantics.rows p R) ++ suffix) [])
        (RecordPrograms.state ports next false true true
          (RecordPrograms.unread (CoefficientSearchSemantics.test p A R)
            (CoefficientSearchSemantics.rows p R) suffix) []) := by
  obtain ⟨n,next,bits,hn,hi,hbits,hgood,hout,he⟩ := BlockSearchProgram.searchCommand_eval
    ports callback 21 (CoefficientSearchSemantics.test p A R)
    (fun _ => callbackBudget A R (width p)) (Invariant p A R alphabet)
    (fun bits => bits ∈ CoefficientSearchSemantics.rows p R)
    (callback_contract p A R alphabet) (CoefficientSearchSemantics.rows p R)
    suffix base (fun _ h => h) hbase
    (CoefficientSearchSemantics.exists_success p h2 A R) tag present found
  obtain ⟨v,hv,hvGood⟩ := (CoefficientSearchSemantics.test_iff p A R bits hbits).mp hgood
  refine ⟨n,next,v,hn,hi,hout.trans hv.symm,hvGood,he⟩

end SubexponentialSAT.Subexp.CoefficientSearchProgram

end OAI.Algorithms
