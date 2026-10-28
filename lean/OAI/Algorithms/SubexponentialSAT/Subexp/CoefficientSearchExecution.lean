import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientSearchGeneration
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientSearchScan
import OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreBounds

namespace OAI.Algorithms

/-! Full normalized coefficient search from the actual scalar-token alphabet.
The finite tuple generator and first-success scan use one fixed program. -/

namespace SubexponentialSAT.Subexp.CoefficientSearchProgram

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

open BitProgram StructuredCalls SubexpScanPrimitives MatrixWordEncoding

variable (p : ℕ) [Fact p.Prime]

theorem invariant_recordState (A R : ℕ) (alphabet : List Bool) (base : Data)
    (hbase : Invariant p A R alphabet base) (tag present found : Bool)
    (source payload : List Bool) :
    Invariant p A R alphabet (RecordPrograms.state ports base tag present found source payload) := by
  rcases hbase with ⟨regs,g,neg,ok,t,pr,f,selected,oldSource,oldPayload,rfl,hlen⟩
  refine ⟨regs,g,neg,ok,tag,present,found,selected,source,payload,?_,hlen⟩
  apply state_ext
  · funext j
    fin_cases j <;> simp [RecordPrograms.state,ports,wide]
  · funext j
    fin_cases j <;> simp [RecordPrograms.state,ports,wide]

def searchBudget (A R : ℕ) : ℕ :=
  7 * R + TupleProgram.powerCost (CoefficientSearchSemantics.scalarTokens p) R [[]] + 23 +
    RecordPrograms.budget (fun _ => callbackBudget A R (width p))
      (CoefficientSearchSemantics.rows p R)

theorem command_eval (h2 : (2 : ZMod p) ≠ 0) (A R : ℕ) (regs : Fin 8 → Bool)
    (g neg ok tag present found : Bool) :
    ∃ (n : ℕ) (final : Data) (v : Fin R → ZMod p), n + 1 ≤ searchBudget p A R ∧
      Eval command n (inputState p A R regs g neg ok tag present found) final ∧
      Invariant p A R (ProgramEncoding.encodeRecords (CoefficientSearchSemantics.scalarTokens p)) final ∧
      final.stacks 21 = CoefficientSearchSemantics.encode p v ∧
      (∀ d < R, CoefficientDynamics.evaluate (List.ofFn v) (A + d) = (-1 : ZMod p)^(A + d)) := by
  obtain ⟨ng,hg,middle,eg,hi,hsource,hpayload,_⟩ :=
    generate_eval p A R regs g neg ok tag present found [] (by simp)
  obtain ⟨ns,last,v,hs,hl,hout,hv,es⟩ := search_eval p A R
    (ProgramEncoding.encodeRecords (CoefficientSearchSemantics.scalarTokens p)) h2 middle hi
    (middle.regs 11) (middle.regs 12) (middle.regs 13) []
  have hstart : RecordPrograms.state ports middle (middle.regs 11) (middle.regs 12) (middle.regs 13)
      (ProgramEncoding.encodeRecords (CoefficientSearchSemantics.rows p R) ++ []) [] = middle := by
    apply RecordPrograms.state_eq_self <;> simp [ports,hsource,hpayload]
  rw [hstart] at es
  let final := RecordPrograms.state ports last false true true
    (RecordPrograms.unread (CoefficientSearchSemantics.test p A R)
      (CoefficientSearchSemantics.rows p R) []) []
  refine ⟨ng + ns,final,v,?_,eg.seq es,?_,?_,hv⟩
  · dsimp [searchBudget]
    omega
  · exact invariant_recordState p A R _ last hl _ _ _ _ _
  · simpa [final,RecordPrograms.state,ports] using hout

/-- The exact scan bound uses the actual number and lengths of generated
candidate records. -/
theorem recordBudget_eq (A R : ℕ) :
    RecordPrograms.budget (fun _ => callbackBudget A R (width p))
      (CoefficientSearchSemantics.rows p R) =
      p ^ R * (6 * (R * (2 * width p + 1)) + callbackBudget A R (width p) + 7) := by
  have hwidth : ∀ bits ∈ CoefficientSearchSemantics.rows p R,
      bits.length = R * (2 * width p + 1) := by
    intro bits hb
    obtain ⟨v,rfl⟩ := (CoefficientSearchSemantics.mem_rows p R bits).mp hb
    exact CoefficientSearchSemantics.encode_length p v
  have h : ∀ rows : List (List Bool),
      (∀ bits ∈ rows, bits.length = R * (2 * width p + 1)) →
      RecordPrograms.budget (fun _ => callbackBudget A R (width p)) rows =
        rows.length * (6 * (R * (2 * width p + 1)) + callbackBudget A R (width p) + 7) := by
    intro rows
    induction rows with
    | nil => simp [RecordPrograms.budget]
    | cons b bs ih =>
      intro hw
      rw [RecordPrograms.budget,hw b (by simp),ih (fun z hz => hw z (by simp [hz]))]
      simp only [List.length_cons]
      ring
  rw [h _ hwidth,CoefficientSearchSemantics.rows_length]

/-- Every exponential term is the actual p^R candidate count. The remaining
factor is a fixed-degree polynomial in the runtime interval and word sizes. -/
theorem searchBudget_le (A R : ℕ) :
    searchBudget p A R ≤ 1000000 * (A + R + 1) * (R + 1) * (width p + 1)^2 * p^R := by
  let B := width p
  let L := R * (2 * B + 1)
  let K := (A + R + 1) * (R + 1) * (B + 1)^2
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hpow : 1 ≤ p ^ R := Nat.one_le_pow _ _ hp
  have ha : 1 ≤ (CoefficientSearchSemantics.scalarTokens p).length := by
    simpa [CoefficientSearchSemantics.scalarTokens,CoefficientSearchSemantics.alphabet] using hp
  have hw : ∀ row ∈ CoefficientSearchSemantics.scalarTokens p, row.length ≤ 2 * B + 1 := by
    intro row hr
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hr
    simp [Encoding.length_frame,B]
  have hg := PairScoreBounds.generated_powerCost_le (CoefficientSearchSemantics.scalarTokens p) R
    (2 * B + 1) ha hw
  have htoken : (CoefficientSearchSemantics.scalarTokens p).length = p := by
    simp [CoefficientSearchSemantics.scalarTokens,CoefficientSearchSemantics.alphabet]
  rw [htoken] at hg
  have hc : callbackBudget A R B ≤ 100000 * K + 14 * L + 7 * A + 21 := by
    have h := CoefficientCheckerProgram.checkerBudget_le A R B
    dsimp [callbackBudget,K,L]
    simp only [Nat.mul_assoc] at h ⊢
    omega
  have hlocal : 800 * (R + 1) * ((R + 1) * (2 * B + 1) + 1) +
      (6 * L + (100000 * K + 14 * L + 7 * A + 21) + 7) + (7 * R + 23) ≤ 1000000 * K := by
    dsimp [K,L]
    ring_nf
    omega
  have hsmall := Nat.mul_le_mul_left (7 * R + 23) hpow
  rw [Nat.mul_one] at hsmall
  rw [searchBudget,recordBudget_eq]
  calc
    _ ≤ 7 * R + (800 * (R + 1) * p ^ R * ((R + 1) * (2 * B + 1) + 1)) + 23 +
        p ^ R * (6 * L + (100000 * K + 14 * L + 7 * A + 21) + 7) := by
      exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_left hg _) _)
        (Nat.mul_le_mul_left _ (by
          change 6 * L + callbackBudget A R B + 7 ≤
            6 * L + (100000 * K + 14 * L + 7 * A + 21) + 7
          omega))
    _ ≤ p ^ R * (800 * (R + 1) * ((R + 1) * (2 * B + 1) + 1) +
        (6 * L + (100000 * K + 14 * L + 7 * A + 21) + 7) + (7 * R + 23)) := by
      calc
        _ = p ^ R * (800 * (R + 1) * ((R + 1) * (2 * B + 1) + 1) +
            (6 * L + (100000 * K + 14 * L + 7 * A + 21) + 7)) + (7 * R + 23) := by ring
        _ ≤ p ^ R * (800 * (R + 1) * ((R + 1) * (2 * B + 1) + 1) +
            (6 * L + (100000 * K + 14 * L + 7 * A + 21) + 7)) + p ^ R * (7 * R + 23) := by
          exact Nat.add_le_add_left (by simpa only [Nat.mul_comm] using hsmall) _
        _ = _ := by ring
    _ ≤ p ^ R * (1000000 * K) := Nat.mul_le_mul_left _ hlocal
    _ = _ := by dsimp [K,B]; ring

theorem program_run (h2 : (2 : ZMod p) ≠ 0) (A R : ℕ) (regs : Fin 8 → Bool)
    (g neg ok tag present found : Bool) :
    ∃ (final : Data) (v : Fin R → ZMod p), RunsIn program (searchBudget p A R)
      ((inputState p A R regs g neg ok tag present found).withPC (some program.entry))
      (final.withPC none) ∧ final.stacks 21 = CoefficientSearchSemantics.encode p v ∧
      (∀ d < R, CoefficientDynamics.evaluate (List.ofFn v) (A + d) = (-1 : ZMod p)^(A + d)) := by
  obtain ⟨n,final,v,hn,he,_,hout,hv⟩ := command_eval p h2 A R regs g neg ok tag present found
  exact ⟨final,v,⟨n + 1,hn,compiled_halt_trace he 25 21⟩,hout,hv⟩

end SubexponentialSAT.Subexp.CoefficientSearchProgram

end OAI.Algorithms
