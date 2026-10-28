import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticCandidateLoad
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticCandidateTest

namespace OAI.Algorithms

/-! # Executable candidate callback and ordered selection contract -/

namespace SubexponentialSAT.SubexpQuarticCandidateContract

open BitProgram StructuredCalls SubexpLiftRing
open SubexpQuarticProducerControl SubexpQuarticCallback
open SubexpQuarticScanInvariant SubexpQuarticDivisorContracts
open SubexpEnumerationPayload SubexpTupleRefinement

def SearchReady (p : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)
    (d : Data) : Prop :=
  (∃ c, Ready p M c d) ∧
  d.stacks 25 = ProgramEncoding.encodeRecords (linearRecords p) ∧
  d.stacks 26 = ProgramEncoding.encodeRecords (quadraticRecords p) ∧
  d.stacks 23 = [] ∧ d.stacks 24 = [] ∧ d.stacks 27 = [] ∧
  (d.stacks 33).length ≤ 4 * baseWidth p 1 ∧
  (d.stacks 34).length ≤ baseWidth p 1

def callbackCost (p : ℕ) : ℕ :=
  124 * baseWidth p 1 + 120 +
  p * (51000 * (baseWidth p 1 + 1)^2 + 24 * scalarWidth p + 27) +
  p^2 * (76000 * (baseWidth p 1 + 1)^2 + 48 * scalarWidth p + 27)

theorem candidate_state_stack (base : Data) (v pr found : Bool)
    (src out : List Bool) (j : Fin 35) (h28 : j ≠ 28) (h29 : j ≠ 29) :
    (RecordPrograms.state candidatePorts base v pr found src out).stacks j = base.stacks j :=
  RecordPrograms.state_stack_frame candidatePorts base v pr found src out j h28 h29

theorem ready_candidate_state (p : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (c : Fin 4 → ZMod p)
    (base : Data) (h : Ready p M c base) (v pr found : Bool) (src out : List Bool) :
    Ready p M c (RecordPrograms.state candidatePorts base v pr found src out) := by
  obtain ⟨bank, hb, hm, hc, h30, h32, h31⟩ := h
  refine ⟨bank, ?_, hm, hc, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (candidate_state_stack base v pr found src out (bankPort i)
        (bankPort_ne_large i 28 (by decide)) (bankPort_ne_large i 29 (by decide))).trans (hb.1 i)
    · intro i
      have hi := workPort_range i
      have h28 : workPort i ≠ 28 := by intro he; have := congrArg Fin.val he; omega
      have h29 : workPort i ≠ 29 := by intro he; have := congrArg Fin.val he; omega
      exact (candidate_state_stack base v pr found src out (workPort i) h28 h29).trans (hb.2.1 i)
    · exact (candidate_state_stack base v pr found src out 22 (by decide) (by decide)).trans hb.2.2
  · exact (candidate_state_stack base v pr found src out 30 (by decide) (by decide)).trans h30
  · exact (candidate_state_stack base v pr found src out 32 (by decide) (by decide)).trans h32
  · rw [candidate_state_stack base v pr found src out 31 (by decide) (by decide)]
    exact h31

theorem searchReady_candidate_state (p : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (base : Data) (h : SearchReady p M base)
    (v pr found : Bool) (src out : List Bool) :
    SearchReady p M (RecordPrograms.state candidatePorts base v pr found src out) := by
  obtain ⟨⟨c, hc⟩, h25, h26, h23, h24, h27, h33, h34⟩ := h
  refine ⟨⟨c, ready_candidate_state p M c base hc v pr found src out⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (candidate_state_stack base v pr found src out 25 (by decide) (by decide)).trans h25
  · exact (candidate_state_stack base v pr found src out 26 (by decide) (by decide)).trans h26
  · exact (candidate_state_stack base v pr found src out 23 (by decide) (by decide)).trans h23
  · exact (candidate_state_stack base v pr found src out 24 (by decide) (by decide)).trans h24
  · exact (candidate_state_stack base v pr found src out 27 (by decide) (by decide)).trans h27
  · simpa only [candidate_state_stack base v pr found src out 33 (by decide) (by decide)] using h33
  · simpa only [candidate_state_stack base v pr found src out 34 (by decide) (by decide)] using h34

/-- The outer iterator's callback premise is discharged by concrete byte
loading, scalar calls, divisor scans, and flag-setting instructions. -/
theorem candidate_contract (p : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) :
    RecordPrograms.CallbackContractWithOn candidatePorts candidateCallback
      (SubexpQuarticByteSpec.candidateTest p) (fun _ => callbackCost p)
      (SearchReady p M) (fun bits _ b => b.stacks 33 = bits)
      (fun bits => bits ∈ SubexpQuarticSelector.candidateRecords p) := by
  intro bits tail base hbits hbase
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hbits
  let bits := encodeTuple (scalarCode p) c
  let start := RecordPrograms.state candidatePorts base false true false tail bits.reverse
  have hs : SearchReady p M start :=
    searchReady_candidate_state p M base hbase false true false tail bits.reverse
  obtain ⟨⟨old, hold⟩, hs25, hs26, hs23, hs24, hs27, hs33, hs34⟩ := hs
  have hinput : start.stacks 29 = bits.reverse :=
    RecordPrograms.state_payload candidatePorts base false true false tail bits.reverse
  obtain ⟨n₁, a, hn₁, he₁, ha, ha24, ha29, ha33, haf, har⟩ :=
    SubexpQuarticCandidateLoad.load_eval p M c old start hold hinput hs24 hs27 hs33
  have ha25 : a.stacks 25 = ProgramEncoding.encodeRecords (linearRecords p) :=
    (haf 25 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs25
  have ha26 : a.stacks 26 = ProgramEncoding.encodeRecords (quadraticRecords p) :=
    (haf 26 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs26
  have ha27 : a.stacks 27 = [] :=
    (haf 27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs27
  have ha23 : a.stacks 23 = [] :=
    (haf 23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs23
  obtain ⟨n₂, next, hn₂, he₂, hnext, hframe, h23, h24, h11, h12, h13⟩ :=
    SubexpQuarticCandidateTest.test_eval p M c a ha ha25 ha26 ha27 ha23 ha24
  have h33 : next.stacks 33 = bits := (hframe 33 (by decide)).trans ha33
  have hflag : next.regs 13 = SubexpQuarticByteSpec.candidateTest p bits := by
    simpa only [bits, SubexpQuarticByteSpec.candidateTest_block] using h13
  have hready : SearchReady p M next := by
    refine ⟨⟨c, hnext⟩, (hframe 25 (by decide)).trans ha25,
      (hframe 26 (by decide)).trans ha26, h23, h24, (hframe 27 (by decide)).trans ha27, ?_, ?_⟩
    · rw [h33]
      exact (SubexpQuarticCandidateLoad.coefficientWords_length p c).le
    · rw [hframe 34 (by decide), haf 34 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hs34
  have h28 : next.stacks 28 = tail := by
    rw [hframe 28 (by decide), haf 28 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact RecordPrograms.state_source candidatePorts base false true false tail bits.reverse
  have h29 : next.stacks 29 = [] := (hframe 29 (by decide)).trans ha29
  have hend : RecordPrograms.state candidatePorts next false true
      (SubexpQuarticByteSpec.candidateTest p bits) tail [] = next :=
    RecordPrograms.state_eq_self candidatePorts next _ _ _ _ _ h11 h12 hflag h28 h29
  refine ⟨n₁ + n₂, next, ?_, hready, h33, ?_⟩
  · dsimp [callbackCost]
    omega
  · rw [hend]
    exact Eval.seq he₁ he₂

/-- Starting with physically generated tables and a prepared scalar bank,
the fixed search controller emits the exact first irreducible quartic. -/
theorem search_eval (p : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (base : Data) (hb : SearchReady p M base)
    (h28 : base.stacks 28 =
      ProgramEncoding.encodeRecords (SubexpQuarticSelector.candidateRecords p))
    (h29 : base.stacks 29 = []) :
    ∃ n next,
      n ≤ 3 + p^4 * (24 * scalarWidth p + callbackCost p + 7) ∧
      Eval search n base next ∧ SearchReady p M next ∧
      next.stacks 33 = encodeTuple (scalarCode p) (QuarticSearch.coefficients p) ∧
      next.stacks 28 = RecordPrograms.unread (SubexpQuarticByteSpec.candidateTest p)
        (SubexpQuarticSelector.candidateRecords p) [] ∧ next.stacks 29 = [] := by
  obtain ⟨n, out, hn, ho, h33, he⟩ := SubexpQuarticSelector.select_eval p
    candidatePorts candidateCallback 33 (SubexpQuarticByteSpec.candidateTest p) (callbackCost p)
    (SearchReady p M) (SubexpQuarticByteSpec.candidateTest_block p) (candidate_contract p M)
    base hb [] (base.regs 11) (base.regs 12) (base.regs 13)
  have hstart : RecordPrograms.state candidatePorts base (base.regs 11) (base.regs 12)
      (base.regs 13) (ProgramEncoding.encodeRecords (SubexpQuarticSelector.candidateRecords p) ++ []) [] =
      base := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · change base.stacks 28 = _
      simpa only [List.append_nil] using h28
    · exact h29
  rw [hstart] at he
  let next := RecordPrograms.state candidatePorts out false true true
    (RecordPrograms.unread (SubexpQuarticByteSpec.candidateTest p)
      (SubexpQuarticSelector.candidateRecords p) []) []
  refine ⟨n, next, hn, he,
    searchReady_candidate_state p M out ho false true true _ [], ?_, ?_, ?_⟩
  · exact (candidate_state_stack out false true true _ [] 33 (by decide) (by decide)).trans h33
  · exact RecordPrograms.state_source candidatePorts out false true true _ []
  · exact RecordPrograms.state_payload candidatePorts out false true true _ []

end SubexponentialSAT.SubexpQuarticCandidateContract

end OAI.Algorithms
