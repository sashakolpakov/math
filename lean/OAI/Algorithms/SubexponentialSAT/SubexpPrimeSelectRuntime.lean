import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeIntervalProgram
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeCandidateRuntime

namespace OAI.Algorithms

/-!
# Measured bounds for the concrete prime selector

Every bound in this module is attached to the actual fixed program. Candidate
tests use the proved trial-division runtime and storage bounds. The invariant
keeps the endpoint, word-width, and workspace budgets fixed across iterations.
-/

namespace SubexponentialSAT.SubexpPrimeSelectRuntime

open BitProgram StructuredProgram StructuredCalls CounterPrograms
open SubexpEnumerationProgram
open SubexpPrimeIntervalProgram

abbrev State := StructuredProgram.State 9 12

def workspaceBound (B K H : ℕ) : ℕ := B + K + H + 1

structure SearchInvariant (B K H : ℕ) (a : State) : Prop where
  lower : 3 ≤ value (a.stacks 9)
  total : value (a.stacks 9) + value (a.stacks 10) ≤ H
  current : (a.stacks 9).length + value (a.stacks 10) ≤ K
  remaining : (a.stacks 10).length ≤ B
  scratch : a.stacks 11 = []
  work : ∀ i : Fin 12, i ≠ 9 → i ≠ 10 → i ≠ 11 →
    (a.stacks i).length ≤ workspaceBound B K H

theorem SearchInvariant.all_words {B K H : ℕ} {a : State}
    (h : SearchInvariant B K H a) (hs : a.stacks 11 = []) :
    ∀ i : Fin 12, (a.stacks i).length ≤ workspaceBound B K H := by
  intro i
  by_cases h9 : i = 9
  · subst i
    have := h.current
    unfold workspaceBound
    omega
  by_cases h10 : i = 10
  · subst i
    exact h.remaining.trans (by unfold workspaceBound; omega)
  by_cases h11 : i = 11
  · subst i
    simp [hs]
  exact h.work i h9 h10 h11

theorem SearchInvariant.after_body {B K H : ℕ} {a b : State} {n : ℕ}
    (h : SearchInvariant B K H a)
    (he : StructuredCalls.Eval SubexpPrimeCandidateProgram.candidateTest n a b) :
    SearchInvariant B K H b := by
  obtain ⟨hc, hr, hs, hi⟩ := SubexpPrimeCandidateProgram.candidateTest_frame he
  have hw := SubexpPrimeCandidateRuntime.candidateTest_final_width he h.lower
  refine ⟨?_, ?_, ?_, ?_, hs.trans h.scratch, ?_⟩
  · simpa only [hc] using h.lower
  · simpa only [hc, hr] using h.total
  · simpa only [hc, hr] using h.current
  · simpa only [hr] using h.remaining
  · intro i hi9 hi10 hi11
    have hv10 : i.val ≠ 10 := by
      intro hv
      apply hi10
      exact Fin.ext hv
    have hv11 : i.val ≠ 11 := by
      intro hv
      apply hi11
      exact Fin.ext hv
    have hlt : i.val < 10 := by have := i.isLt; omega
    let j : Fin 10 := ⟨i.val, hlt⟩
    have hj : SubexpPrimeCandidateProgram.stackMap j = i := by apply Fin.ext; rfl
    rw [← hj]
    apply (hw j).trans
    have hcur := h.current
    have htot := h.total
    unfold workspaceBound
    omega

theorem SearchInvariant.after_next {B K H : ℕ} {a : State}
    (h : SearchInvariant B K H a) (hp : 0 < value (a.stacks 10)) :
    SearchInvariant B K H (nextState ports a) := by
  have hc : (nextState ports a).stacks 9 = ripple true (a.stacks 9) :=
    nextState_current ports a
  have hr : (nextState ports a).stacks 10 = ripple false (a.stacks 10) :=
    nextState_remaining ports a
  have hv := value_decrement hp
  have hw := ripple_length_le true (a.stacks 9)
  refine ⟨?_, ?_, ?_, ?_, nextState_scratch ports a, ?_⟩
  · rw [hc, value_increment]
    have := h.lower
    omega
  · rw [hc, hr, value_increment]
    have := h.total
    omega
  · rw [hc, hr]
    have := h.current
    omega
  · rw [hr, decrement_length hp]
    exact h.remaining
  · intro i h9 h10 h11
    rw [nextState_other_stack ports a i h9 h10 h11]
    exact h.work i h9 h10 h11

theorem SearchInvariant.of_stacks_eq {B K H : ℕ} {a b : State}
    (h : SearchInvariant B K H a) (hs : b.stacks = a.stacks) :
    SearchInvariant B K H b := by
  rcases h with ⟨hl, ht, hc, hr, hsc, hw⟩
  exact ⟨by simpa only [hs] using hl, by simpa only [hs] using ht,
    by simpa only [hs] using hc, by simpa only [hs] using hr,
    by simpa only [hs] using hsc, by simpa only [hs] using hw⟩

def candidateBound (B K H : ℕ) : ℕ :=
  10000 * (workspaceBound B K H + H + 3) ^ 3 + 1

theorem candidate_steps {B K H : ℕ} {a b : State} {n : ℕ}
    (h : SearchInvariant B K H a) (hs : a.stacks 11 = [])
    (he : StructuredCalls.Eval SubexpPrimeCandidateProgram.candidateTest n a b) :
    n ≤ candidateBound B K H := by
  have hn := SubexpPrimeCandidateRuntime.candidateTest_steps_le_polynomial he
    (workspaceBound B K H)
    (fun i => h.all_words hs (SubexpPrimeCandidateProgram.stackMap i))
    (by have := h.lower; omega)
  have hN : value (a.stacks 9) ≤ H := by have := h.total; omega
  have hp := Nat.pow_le_pow_left
    (Nat.add_le_add_right (Nat.add_le_add_left hN (workspaceBound B K H)) 3) 3
  unfold candidateBound
  omega

theorem search_body_contract (B K H : ℕ) :
    SubexpFirstSuccessProgram.BodyContract ports 8
      SubexpPrimeCandidateProgram.candidateTest SubexpPackingParameters.primeTest
      (SearchInvariant B K H) := by
  intro a ha hs
  obtain ⟨n, b, he, hp, hc, hr, hsc, hi⟩ :=
    SubexpPrimeCandidateProgram.candidateTest_correct a (by have := ha.lower; omega)
  refine ⟨n, b, he, ha.after_body he, hc, hr, hsc.trans hs, ?_⟩
  apply Bool.eq_iff_iff.mpr
  rw [show ports.current = (9 : Fin 12) from rfl]
  simpa only [SubexpPackingParameters.primeTest, decide_eq_true_eq] using hp

theorem visits_invariant {B K H : ℕ} {labels costs : List ℕ} {n : ℕ} {a b : State}
    (hv : SubexpFirstSuccessProgram.Visits ports 8
      SubexpPrimeCandidateProgram.candidateTest labels costs n a b)
    (ha : SearchInvariant B K H a)
    (hcount : labels.length ≤ value (a.stacks 10)) : SearchInvariant B K H b := by
  induction hv with
  | exhausted => exact ha
  | found hg he hc hr hs hf =>
      exact (ha.after_body he).of_stacks_eq rfl
  | @miss d e f nb nt labels costs hg he hc hr hs hf ht ih =>
      have hp : 0 < value (e.stacks 10) := by
        change e.stacks 10 = d.stacks 10 at hr
        rw [hr]
        simp only [List.length_cons] at hcount
        omega
      apply ih ((ha.after_body he).after_next hp)
      change value ((nextState ports e).stacks ports.remaining) ≥ labels.length
      rw [nextState_remaining]
      change labels.length ≤ value (ripple false (e.stacks 10))
      have hv := value_decrement hp
      change e.stacks 10 = d.stacks 10 at hr
      rw [hr] at hv ⊢
      simp only [List.length_cons] at hcount
      omega

def intervalBound (B C F : ℕ) : ℕ :=
  8 * B + 9 + F *
    (candidateBound B (B + F) (C + F) + 8 * (B + F) + 16 * B + 25)

theorem interval_bounded_with_words (a : State) (B : ℕ)
    (hB : ∀ i : Fin 12, (a.stacks i).length ≤ B)
    (hcandidate : 3 ≤ value (a.stacks 9)) (hs : a.stacks 11 = []) :
    ∃ n b, StructuredCalls.Eval intervalSearch n a b ∧
      n ≤ intervalBound B (value (a.stacks 9)) (value (a.stacks 10)) ∧
      (b.stacks 9).length ≤ B + value (a.stacks 10) ∧
      searchResult b = (ParameterOrder.scanFrom SubexpPackingParameters.primeTest
        (value (a.stacks 9)) (value (a.stacks 10))).1 ∧
      ∀ i : Fin 12, (b.stacks i).length ≤
        workspaceBound B (B + value (a.stacks 10))
          (value (a.stacks 9) + value (a.stacks 10)) := by
  let K := B + value (a.stacks 10)
  let H := value (a.stacks 9) + value (a.stacks 10)
  have ha : SearchInvariant B K H a := by
    refine ⟨hcandidate, le_rfl, Nat.add_le_add_right (hB 9) _, hB 10, hs, ?_⟩
    intro i _ _ _
    exact (hB i).trans (by unfold workspaceBound; omega)
  have hst := SubexpFirstSuccessProgram.startState_stacks ports 8 a hs
  have hstart := ha.of_stacks_eq hst
  obtain ⟨labels, costs, n, b, he, ⟨nt, hv, htime⟩, hresult, hlen, hcostlen, hn, hscr⟩ :=
    SubexpFirstSuccessProgram.search_measured ports 8 success_frame
      SubexpPrimeCandidateProgram.candidateTest SubexpPackingParameters.primeTest
      (SearchInvariant B K H) (search_body_contract B K H)
      (fun _ h _ hp => h.after_next hp) a hs hstart
  have hcount : labels.length ≤ value (a.stacks 10) := by
    rw [hlen]
    exact ParameterOrder.scanFrom_calls_le _ _ _
  have hcount' : labels.length ≤ value
      ((SubexpFirstSuccessProgram.startState ports 8 a).stacks 10) := by
    simpa only [hst] using hcount
  have hb := visits_invariant hv hstart hcount'
  change n ≤ costs.sum + 8 * (a.stacks 10).length + 9 +
    value (a.stacks 10) * (8 * ((a.stacks 9).length + value (a.stacks 10)) +
      16 * (a.stacks 10).length + 25) at hn
  have hsum := hv.costs_le_of_invariant (SearchInvariant B K H) hstart
    (candidateBound B K H) hcount'
    (fun nb d e hde hd => ⟨hd.after_body hde, candidate_steps hd hd.scratch hde⟩)
    (fun _ h _ hp => h.after_next hp)
  refine ⟨n, b, he, ?_, ?_, hresult, hb.all_words hb.scratch⟩
  · have hprod := Nat.mul_le_mul_right (candidateBound B K H) hcount
    have h10 := hB 10
    have h9 := hB 9
    have hcontroller := Nat.mul_le_mul_left (value (a.stacks 10))
      (show 8 * ((a.stacks 9).length + value (a.stacks 10)) +
        16 * (a.stacks 10).length + 25 ≤ 8 * (B + value (a.stacks 10)) + 16 * B + 25 by omega)
    change n ≤ 8 * B + 9 + value (a.stacks 10) *
      (candidateBound B K H + 8 * (B + value (a.stacks 10)) + 16 * B + 25)
    calc
      n ≤ value (a.stacks 10) * candidateBound B K H + 8 * B + 9 +
          value (a.stacks 10) * (8 * (B + value (a.stacks 10)) + 16 * B + 25) := by omega
      _ = _ := by ring
  · have := hb.current
    change (b.stacks 9).length ≤ K
    omega

theorem interval_bounded (a : State) (B : ℕ)
    (hB : ∀ i : Fin 12, (a.stacks i).length ≤ B)
    (hcandidate : 3 ≤ value (a.stacks 9)) (hs : a.stacks 11 = []) :
    ∃ n b, StructuredCalls.Eval intervalSearch n a b ∧
      n ≤ intervalBound B (value (a.stacks 9)) (value (a.stacks 10)) ∧
      (b.stacks 9).length ≤ B + value (a.stacks 10) ∧
      searchResult b = (ParameterOrder.scanFrom SubexpPackingParameters.primeTest
        (value (a.stacks 9)) (value (a.stacks 10))).1 := by
  obtain ⟨n, b, he, hn, hl, hr, hw⟩ :=
    interval_bounded_with_words a B hB hcandidate hs
  exact ⟨n, b, he, hn, hl, hr⟩

def endpointWordBound (exponent : List Bool) : ℕ :=
  exponent.length + value exponent + 2

theorem endpoint_words {n : ℕ} {b : State} (exponent : List Bool)
    (he : StructuredCalls.Eval endpointCommand n (inputState exponent) b) :
    ∀ i : Fin 12, (b.stacks i).length ≤ endpointWordBound exponent := by
  classical
  obtain ⟨m, d, hm, hd, hr⟩ := SubexpEndpointProgram.lifted_output
    SubexpPrimeProgram.zeroRegister endpointStack SubexpPrimeProgram.zeroRegister_injective
    endpointStack_injective (inputState exponent) (fun _ => false) exponent
  rw [endpoint_initial] at hr
  have heq := SubexpPrimeProgram.eval_result_unique he hr 0 9
  have hl := SubexpEndpointProgram.output_lengths exponent d hd
  have hlocal : ∀ i : Fin 6, (d.stacks i).length ≤ endpointWordBound exponent := by
    intro i
    fin_cases i
    · change (d.stacks 0).length ≤ endpointWordBound exponent
      rw [hd.2.1]
      unfold endpointWordBound
      omega
    · change (d.stacks 1).length ≤ endpointWordBound exponent
      rw [hd.2.2.1]
      simp
    · change (d.stacks 2).length ≤ endpointWordBound exponent
      rw [hl.1]
      unfold endpointWordBound
      omega
    · change (d.stacks 3).length ≤ endpointWordBound exponent
      have := hl.2.1
      unfold endpointWordBound
      omega
    · change (d.stacks 4).length ≤ endpointWordBound exponent
      rw [hl.2.2.1]
      unfold endpointWordBound
      omega
    · change (d.stacks 5).length ≤ endpointWordBound exponent
      rw [hl.2.2.2]
      unfold endpointWordBound
      omega
  intro i
  rw [heq]
  by_cases hi : ∃ j, endpointStack j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [StructuredCalls.embedState_stack _ _ _ _ endpointStack_injective]
    exact hlocal j
  · rw [StructuredCalls.embedState_stack_frame _ _ _ _ _ hi]
    unfold inputState StructuredProgram.ioState endpointWordBound
    change (if i = (0 : Fin 12) then exponent else []).length ≤
      exponent.length + value exponent + 2
    split
    · omega
    · simp

theorem finishSelection_bounded (a : State) :
    ∃ n b, StructuredCalls.Eval finishSelection n a b ∧
      n ≤ 2 * (a.stacks 9).length + 7 ∧
      value (b.stacks 9) = (searchResult a).getD 3 := by
  cases hf : a.regs 8 with
  | false =>
      refine ⟨2 * (a.stacks 9).length + 6 + 1, defaultState a,
        .ite_false hf (writeDefault_eval a), by omega, ?_⟩
      simp [ searchResult, SubexpFirstSuccessProgram.result, hf, value]
  | true =>
      refine ⟨1, a, .ite_true hf (.base (.skip a)), by omega, ?_⟩
      simp [searchResult, SubexpFirstSuccessProgram.result, hf, ports]

theorem finishSelection_length {a b : State} {n : ℕ}
    (he : StructuredCalls.Eval finishSelection n a b) :
    (b.stacks 9).length ≤ max 2 (a.stacks 9).length := by
  cases hf : a.regs 8 with
  | false =>
      have hr : StructuredCalls.Eval finishSelection
          (2 * (a.stacks 9).length + 6 + 1) a (defaultState a) :=
        .ite_false hf (writeDefault_eval a)
      rw [SubexpPrimeProgram.eval_result_unique he hr 0 9]
      change 2 ≤ max 2 (a.stacks 9).length
      exact le_max_left _ _
  | true =>
      have hr : StructuredCalls.Eval finishSelection 1 a a :=
        .ite_true hf (.base (.skip a))
      rw [SubexpPrimeProgram.eval_result_unique he hr 0 9]
      exact le_max_right _ _

def selectorBound (exponent : List Bool) : ℕ :=
  SubexpEndpointProgram.runtimeBound exponent +
    intervalBound (endpointWordBound exponent) (2 ^ value exponent + 1) (2 ^ value exponent - 1) +
    2 * (endpointWordBound exponent + (2 ^ value exponent - 1)) + 7

/-- All nested candidate and divisor loops are charged. The bound contains
only the encoded exponent's bit length, value, and its generated power of two. -/
theorem primeSelect_bounded (exponent : List Bool) :
    ∃ n b, StructuredCalls.Eval primeSelectCmd n (inputState exponent) b ∧
      n ≤ selectorBound exponent ∧
      value (b.stacks 9) = selectedPrime (value exponent) ∧
      (b.stacks 9).length ≤ endpointWordBound exponent + (2 ^ value exponent - 1) := by
  obtain ⟨ne, a, he, hne, hc, hr, hs⟩ := endpointCommand_correct exponent
  have hB := endpoint_words exponent he
  have hscan : ∃ ns b, StructuredCalls.Eval intervalSearch ns a b ∧
      ns ≤ intervalBound (endpointWordBound exponent)
        (2 ^ value exponent + 1) (2 ^ value exponent - 1) ∧
      (b.stacks 9).length ≤ endpointWordBound exponent + (2 ^ value exponent - 1) := by
    by_cases hz : value exponent = 0
    · have hr0 : value (a.stacks 10) = 0 := by simpa [hz] using hr
      have hexit := SubexpFirstSuccessProgram.search_empty ports 8 success_frame
        SubexpPrimeCandidateProgram.candidateTest a hs hr0
      refine ⟨8 * (a.stacks 10).length + 9,
        SubexpFirstSuccessProgram.startState ports 8 a, hexit.1, ?_, ?_⟩
      · simp only [hz, pow_zero, Nat.sub_self, intervalBound, Nat.zero_mul, Nat.add_zero]
        have := hB 10
        omega
      · rw [SubexpFirstSuccessProgram.startState_stacks ports 8 a hs]
        have := hB 9
        omega
    · have hpow : 2 ≤ 2 ^ value exponent := by
        have ht := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
          (show 1 ≤ value exponent by omega)
        simpa only [pow_one] using ht
      obtain ⟨ns, b, hb, hnb, hl, hout⟩ := interval_bounded a
        (endpointWordBound exponent) hB (by omega) hs
      exact ⟨ns, b, hb, by simpa only [hc, hr] using hnb,
        by simpa only [hr] using hl⟩
  obtain ⟨ns, b, hb, hns, hl⟩ := hscan
  obtain ⟨nf, c, hf, hnf, hout⟩ := finishSelection_bounded b
  have hrun : StructuredCalls.Eval primeSelectCmd (ne + ns + nf) (inputState exponent) c :=
    (he.seq hb).seq hf
  obtain ⟨n, d, hd, hvalue⟩ := primeSelect_correct exponent
  have heq := SubexpPrimeProgram.eval_result_unique hrun hd 0 9
  refine ⟨ne + ns + nf, c, hrun, ?_, ?_, ?_⟩
  · unfold selectorBound
    omega
  · simpa only [heq] using hvalue
  · exact (finishSelection_length hf).trans (max_le
      (by unfold endpointWordBound; omega) hl)

theorem primeSelect_output_length {n : ℕ} {b : State} (exponent : List Bool)
    (he : StructuredCalls.Eval primeSelectCmd n (inputState exponent) b) :
    (b.stacks 9).length ≤ endpointWordBound exponent + (2 ^ value exponent - 1) := by
  obtain ⟨steps, c, hc, htime, hvalue, hlength⟩ := primeSelect_bounded exponent
  rw [SubexpPrimeProgram.eval_result_unique he hc 0 9]
  exact hlength

theorem finishSelection_all_words {a b : State} {n B : ℕ}
    (he : StructuredCalls.Eval finishSelection n a b)
    (hB : ∀ i : Fin 12, (a.stacks i).length ≤ B) (h2 : 2 ≤ B) :
    ∀ i : Fin 12, (b.stacks i).length ≤ B := by
  cases hf : a.regs 8 with
  | false =>
      have hr : StructuredCalls.Eval finishSelection
          (2 * (a.stacks 9).length + 6 + 1) a (defaultState a) :=
        .ite_false hf (writeDefault_eval a)
      rw [SubexpPrimeProgram.eval_result_unique he hr 0 9]
      intro i
      by_cases hi : i = 9
      · subst i
        exact h2
      · simpa [defaultState, hi] using hB i
  | true =>
      have hr : StructuredCalls.Eval finishSelection 1 a a :=
        .ite_true hf (.base (.skip a))
      rw [SubexpPrimeProgram.eval_result_unique he hr 0 9]
      exact hB

def selectorWordBound (exponent : List Bool) : ℕ :=
  workspaceBound (endpointWordBound exponent)
    (endpointWordBound exponent + (2 ^ value exponent - 1))
    ((2 ^ value exponent + 1) + (2 ^ value exponent - 1))

theorem selectorWordBound_eq (exponent : List Bool) :
    selectorWordBound exponent =
      2 * endpointWordBound exponent + 3 * 2 ^ value exponent := by
  have hp : 1 ≤ 2 ^ value exponent := Nat.one_le_pow _ _ (by decide)
  unfold selectorWordBound workspaceBound
  omega

/-- All twelve final words are bounded, so a caller can charge explicit
workspace cleanup after relocating this routine into a persistent store. -/
theorem primeSelect_all_words {n : ℕ} {b : State} (exponent : List Bool)
    (he : StructuredCalls.Eval primeSelectCmd n (inputState exponent) b) :
    ∀ i : Fin 12, (b.stacks i).length ≤ selectorWordBound exponent := by
  obtain ⟨ne, a, hep, hne, hc, hr, hs⟩ := endpointCommand_correct exponent
  have hB := endpoint_words exponent hep
  have hbase : endpointWordBound exponent ≤ selectorWordBound exponent := by
    unfold selectorWordBound workspaceBound
    omega
  have htwo : 2 ≤ selectorWordBound exponent := by
    unfold endpointWordBound at hbase
    omega
  have hscan : ∃ ns c, StructuredCalls.Eval intervalSearch ns a c ∧
      ∀ i : Fin 12, (c.stacks i).length ≤ selectorWordBound exponent := by
    by_cases hz : value exponent = 0
    · have hr0 : value (a.stacks 10) = 0 := by simpa [hz] using hr
      have hexit := SubexpFirstSuccessProgram.search_empty ports 8 success_frame
        SubexpPrimeCandidateProgram.candidateTest a hs hr0
      refine ⟨8 * (a.stacks 10).length + 9,
        SubexpFirstSuccessProgram.startState ports 8 a, hexit.1, ?_⟩
      intro i
      rw [SubexpFirstSuccessProgram.startState_stacks ports 8 a hs]
      exact (hB i).trans hbase
    · have hpow : 2 ≤ 2 ^ value exponent := by
        have ht := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
          (show 1 ≤ value exponent by omega)
        simpa only [pow_one] using ht
      obtain ⟨ns, c, hrun, htime, hlen, hresult, hwords⟩ :=
        interval_bounded_with_words a (endpointWordBound exponent) hB (by omega) hs
      refine ⟨ns, c, hrun, ?_⟩
      simpa only [hc, hr, selectorWordBound] using hwords
  obtain ⟨ns, c, hcs, hw⟩ := hscan
  obtain ⟨nf, d, hfinish, hvalue⟩ := finishSelection_correct c
  have hd := finishSelection_all_words hfinish hw htwo
  have hrun : StructuredCalls.Eval primeSelectCmd (ne + ns + nf) (inputState exponent) d :=
    (hep.seq hcs).seq hfinish
  rw [SubexpPrimeProgram.eval_result_unique he hrun 0 9]
  exact hd

theorem primeSelect_schedule_runsIn (n : ℕ) (exponent : List Bool)
    (hexponent : value exponent = SubexpPackingParameters.u n) :
    ∃ b : State, BitProgram.RunsIn primeSelectProgram (selectorBound exponent + 1)
      ((inputState exponent).withPC (some primeSelectProgram.entry)) (b.withPC none) ∧
      value (b.stacks 9) = SubexpPackingParameters.p n := by
  obtain ⟨steps, b, he, hs, hp, hlen⟩ := primeSelect_bounded exponent
  refine ⟨b, ⟨steps + 1, Nat.add_le_add_right hs 1,
    StructuredCalls.compiled_halt_trace he 0 9⟩, ?_⟩
  exact hp.trans (by rw [hexponent, selectedPrime_eq_schedule])

theorem primeSelect_schedule_primitive_runsIn (n : ℕ) (exponent : List Bool)
    (hexponent : value exponent = SubexpPackingParameters.u n) :
    ∃ b : State, Computation.RunsIn (BitProgram.primitive primeSelectProgram).step
      (BitProgram.primitiveOverhead primeSelectProgram * (selectorBound exponent + 1))
      (BitProgram.primitiveCfg primeSelectProgram
        ((inputState exponent).withPC (some primeSelectProgram.entry)))
      (BitProgram.primitiveCfg primeSelectProgram (b.withPC none)) ∧
      value (b.stacks 9) = SubexpPackingParameters.p n := by
  obtain ⟨b, hr, hp⟩ := primeSelect_schedule_runsIn n exponent hexponent
  exact ⟨b, BitProgram.primitive_execution _ hr, hp⟩

theorem intervalBound_le (B C F : ℕ) :
    intervalBound B C F ≤ 1000000 * (B + C + F + 4) ^ 4 := by
  let X := B + C + F + 4
  have hX : 0 < X := by dsimp [X]; omega
  have hF : F ≤ X := by dsimp [X]; omega
  have hbase : workspaceBound B (B + F) (C + F) + (C + F) + 3 ≤ 3 * X := by
    dsimp [workspaceBound, X]
    omega
  have hcube : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ hX
  have hpow := Nat.pow_le_pow_left hbase 3
  have hcb : candidateBound B (B + F) (C + F) ≤ 270001 * X ^ 3 := by
    calc
      _ ≤ 10000 * (3 * X) ^ 3 + 1 := by unfold candidateBound; omega
      _ = 270000 * X ^ 3 + 1 := by ring
      _ ≤ 270001 * X ^ 3 := by omega
  have hX3 : X ≤ X ^ 3 := Nat.le_self_pow (by decide) X
  have hX4 : X ≤ X ^ 4 := Nat.le_self_pow (by decide) X
  have hcontrol : 8 * (B + F) + 16 * B + 25 ≤ 49 * X ^ 3 := by
    have hlinear : 8 * (B + F) + 16 * B + 25 ≤ 49 * X := by dsimp [X]; omega
    omega
  have hinner : candidateBound B (B + F) (C + F) +
      8 * (B + F) + 16 * B + 25 ≤ 270050 * X ^ 3 := by omega
  have hprefix : 8 * B + 9 ≤ 17 * X ^ 4 := by
    have hlinear : 8 * B + 9 ≤ 17 * X := by dsimp [X]; omega
    omega
  change intervalBound B C F ≤ 1000000 * X ^ 4
  calc
    intervalBound B C F ≤ 17 * X ^ 4 + X * (270050 * X ^ 3) :=
      Nat.add_le_add hprefix (Nat.mul_le_mul hF hinner)
    _ = 270067 * X ^ 4 := by ring
    _ ≤ 1000000 * X ^ 4 := Nat.mul_le_mul_right _ (by decide)

/-- A fixed quartic bound in the actual input bit length and generated
interval scale. This bound concerns the finite program's counted instructions. -/
theorem selectorBound_le (exponent : List Bool) :
    selectorBound exponent ≤
      100000000 * (exponent.length + 2 ^ value exponent + 5) ^ 4 := by
  let U := value exponent
  let P := 2 ^ U
  let X := exponent.length + P + 5
  have hUP : U ≤ P := Nat.le_of_lt (show U < 2 ^ U from Nat.lt_two_pow_self)
  have hX : 0 < X := by dsimp [X]; omega
  have hU1 : U + 1 ≤ X := by dsimp [X]; omega
  have hL : exponent.length ≤ X := by dsimp [X]; omega
  have hX2 : X ≤ X ^ 2 := Nat.le_self_pow (by decide) X
  have hX4 : X ≤ X ^ 4 := Nat.le_self_pow (by decide) X
  have h24 : X ^ 2 ≤ X ^ 4 := Nat.pow_le_pow_right hX (by decide)
  have hprod : (U + 1) * exponent.length ≤ X ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hU1 hL
  have hend : SubexpEndpointProgram.runtimeBound exponent ≤ 85 * X ^ 4 := by
    rw [SubexpEndpointProgram.runtimeBound_eq]
    change 16 * (U + 1) * exponent.length + 30 * U + 39 ≤ 85 * X ^ 4
    have hrest : 30 * U + 39 ≤ 69 * X ^ 2 := by omega
    have hmul : 16 * (U + 1) * exponent.length ≤ 16 * X ^ 2 := by
      calc
        _ = 16 * ((U + 1) * exponent.length) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hprod
    omega
  have harg : endpointWordBound exponent + (P + 1) + (P - 1) + 4 ≤ 3 * X := by
    dsimp [endpointWordBound, U, X] at *
    omega
  have hinterval : intervalBound (endpointWordBound exponent) (P + 1) (P - 1) ≤
      81000000 * X ^ 4 := by
    calc
      _ ≤ 1000000 * (endpointWordBound exponent + (P + 1) + (P - 1) + 4) ^ 4 :=
        intervalBound_le _ _ _
      _ ≤ 1000000 * (3 * X) ^ 4 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 4)
      _ = _ := by ring
  have hfinish : 2 * (endpointWordBound exponent + (P - 1)) + 7 ≤ 9 * X ^ 4 := by
    have hlinear : 2 * (endpointWordBound exponent + (P - 1)) + 7 ≤ 9 * X := by
      dsimp [endpointWordBound, U, X] at *
      omega
    omega
  change selectorBound exponent ≤ 100000000 * X ^ 4
  unfold selectorBound
  change SubexpEndpointProgram.runtimeBound exponent +
    intervalBound (endpointWordBound exponent) (P + 1) (P - 1) +
    2 * (endpointWordBound exponent + (P - 1)) + 7 ≤ 100000000 * X ^ 4
  omega

theorem primeSelect_schedule_polynomial (n : ℕ) (exponent : List Bool)
    (hexponent : value exponent = SubexpPackingParameters.u n) :
    ∃ b : State, BitProgram.RunsIn primeSelectProgram
      (100000000 * (exponent.length + 2 ^ value exponent + 5) ^ 4 + 1)
      ((inputState exponent).withPC (some primeSelectProgram.entry)) (b.withPC none) ∧
      value (b.stacks 9) = SubexpPackingParameters.p n := by
  obtain ⟨b, hr, hp⟩ := primeSelect_schedule_runsIn n exponent hexponent
  exact ⟨b, hr.mono (Nat.add_le_add_right (selectorBound_le exponent) 1), hp⟩

theorem primeSelect_schedule_primitive_polynomial (n : ℕ) (exponent : List Bool)
    (hexponent : value exponent = SubexpPackingParameters.u n) :
    ∃ b : State, Computation.RunsIn (BitProgram.primitive primeSelectProgram).step
      (BitProgram.primitiveOverhead primeSelectProgram *
        (100000000 * (exponent.length + 2 ^ value exponent + 5) ^ 4 + 1))
      (BitProgram.primitiveCfg primeSelectProgram
        ((inputState exponent).withPC (some primeSelectProgram.entry)))
      (BitProgram.primitiveCfg primeSelectProgram (b.withPC none)) ∧
      value (b.stacks 9) = SubexpPackingParameters.p n := by
  obtain ⟨b, hr, hp⟩ := primeSelect_schedule_polynomial n exponent hexponent
  exact ⟨b, BitProgram.primitive_execution _ hr, hp⟩

end SubexponentialSAT.SubexpPrimeSelectRuntime

end OAI.Algorithms
