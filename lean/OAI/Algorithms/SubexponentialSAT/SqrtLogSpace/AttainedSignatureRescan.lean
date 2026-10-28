import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CounterLoops

/-! Actual bounded-word predecessor rescan and its uniform source-prefix storage. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

namespace Rescan

theorem workState_fuel_update (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel newFuel : List Bool)
    (fresh : Bool) :
    (workState regs W rows candidate saved predecessor newFuel fresh [] []).stacks =
      Function.update (workState regs W rows candidate saved predecessor fuel fresh [] []).stacks
        19 newFuel := by
  funext i
  fin_cases i <;> simp [workState]

theorem nextState_workState (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) :
    CounterForPrograms.nextState countdownPorts
      (workState regs W rows candidate saved predecessor fuel fresh [] []) =
      workState (CounterForPrograms.nextState countdownPorts
        (workState regs W rows candidate saved predecessor fuel fresh [] [])).regs
        W rows candidate saved predecessor (CounterPrograms.ripple false fuel) fresh [] [] := by
  let a := workState regs W rows candidate saved predecessor fuel fresh [] []
  have hs : (CounterForPrograms.nextState countdownPorts a).stacks =
      Function.update a.stacks 19 (CounterPrograms.ripple false fuel) := by
    funext i
    by_cases hc : i = 19
    · subst i
      rw [Function.update_self]
      exact CounterForPrograms.nextState_counter countdownPorts a
    rw [Function.update_of_ne hc]
    by_cases he : i = 20
    · subst i
      exact CounterForPrograms.nextState_scratch countdownPorts a
    exact (CounterForPrograms.nextState_outside countdownPorts a i hc he).symm
  apply congrArg (StructuredProgram.State.mk _)
  exact hs.trans (workState_fuel_update _ W rows candidate saved predecessor fuel _ fresh).symm

theorem body_scan_eval (W : List Bool) (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (i : ℕ) (hi : i < candidate.val)
    (fuel : List Bool) (regs : Fin 16 → Bool) :
    ∃ nb ≤ bodyBound W (naturalKey W rows h candidate) rows h B, ∃ rb,
      Eval body nb
        (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h i) fuel
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate i)) [] [])
        (workState rb W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h (i + 1)) fuel
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate (i + 1))) [] []) := by
  have hil : i < 2 ^ h := hi.trans candidate.isLt
  have hinext : i + 1 < 2 ^ h := by have := candidate.isLt; omega
  let current := ExecCNFTupleEnumeration.fixedBits h i
  let saved := naturalKey W rows h candidate
  let fresh := !(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate i)
  obtain ⟨nb, hnb, rb, hb⟩ := body_eval regs W rows
    (ExecCNFTupleEnumeration.fixedBits h candidate) saved current fuel fresh
    (by simpa [current] using hlen)
  have hbound : nb ≤ bodyBound W saved rows h B :=
    hnb.trans (bodyCost_le W current saved rows h B (by simp [current]) hlen hwidth)
  have hword : CounterPrograms.ripple true current =
      ExecCNFTupleEnumeration.fixedBits h (i + 1) :=
    Counters.increment_word (⟨i, hil⟩ : Fin (2 ^ h)) hinext
  have hfresh : (fresh && !decide (signatureValue W current rows = saved)) =
      !(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate (i + 1)) := by
    simp [AttainedSignatures.duplicateScan, fresh, saved, current, naturalKey, Bool.not_or]
    rfl
  rw [hword, hfresh] at hb
  exact ⟨nb, hbound, rb, hb⟩

inductive ScanInvariant (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (i : ℕ) (a : Data) : Prop where
  | intro (fuel : List Bool) (hlen : fuel.length = h)
      (hvalue : i + CounterPrograms.value fuel = candidate.val)
      (he : a = workState a.regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h i) fuel
        (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate i)) [] []) :
      ScanInvariant W rows h candidate i a

theorem scan_spec (W : List Bool) (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B) (candidate : Fin (2 ^ h)) :
    ∀ i a, ScanInvariant W rows h candidate i a → a.stacks countdownPorts.scratch = [] →
      0 < CounterPrograms.value (a.stacks countdownPorts.counter) →
      ∃ nb e, nb ≤ bodyBound W (naturalKey W rows h candidate) rows h B ∧ Eval body nb a e ∧
        e.stacks countdownPorts.counter = a.stacks countdownPorts.counter ∧
        e.stacks countdownPorts.scratch = [] ∧
        ScanInvariant W rows h candidate (i + 1) (CounterForPrograms.nextState countdownPorts e) := by
  intro i a hI _ hp
  obtain ⟨fuel, hl, hv, he⟩ := hI
  have hcounter : a.stacks countdownPorts.counter = fuel :=
    congrArg (fun d : Data => d.stacks countdownPorts.counter) he
  have hp' : 0 < CounterPrograms.value fuel := by simpa only [hcounter] using hp
  have hi : i < candidate.val := by omega
  obtain ⟨nb, hnb, rb, hb⟩ := body_scan_eval W rows h B hlen hwidth candidate i hi fuel a.regs
  let e := workState rb W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
    (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h (i + 1)) fuel
    (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate (i + 1))) [] []
  refine ⟨nb, e, hnb, ?_, ?_, rfl, ?_⟩
  · exact Eq.mpr (congrArg (fun d : Data => Eval body nb d e) he) hb
  · exact hcounter.symm
  · refine ⟨CounterPrograms.ripple false fuel,
      (CounterPrograms.decrement_length hp').trans hl, ?_, ?_⟩
    · have hd := CounterPrograms.value_decrement hp'
      omega
    · exact nextState_workState rb W rows _ _ _ fuel _

theorem visits_exists (W : List Bool) (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (remaining : ℕ)
    (i : ℕ) (fuel : List Bool) (regs : Fin 16 → Bool)
    (htotal : i + remaining = candidate.val) (hl : fuel.length = h)
    (hv : CounterPrograms.value fuel = remaining)
    (hf : regs 15 = !(CounterPrograms.isZero fuel)) :
    ∃ costs n out,
      CounterForPrograms.Visits countdownPorts body costs n
        (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h i) fuel
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate i)) [] [])
        (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h candidate)
          (List.replicate h false)
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []) ∧
      costs.sum ≤ remaining * bodyBound W (naturalKey W rows h candidate) rows h B := by
  let a := workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
    (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h i) fuel
    (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate i)) [] []
  have hI : ScanInvariant W rows h candidate i a := ⟨fuel, hl, by omega, rfl⟩
  obtain ⟨costs, n, e, hrun, hIe, _, hcost⟩ := CounterLoops.visits_exists_next
    countdownPorts body (ScanInvariant W rows h candidate)
    (fun _ => bodyBound W (naturalKey W rows h candidate) rows h B)
    (scan_spec W rows h B hlen hwidth candidate) remaining i a hv rfl hf hI
  obtain ⟨finalFuel, hfl, hfv, he⟩ := hIe
  have hzero : CounterPrograms.value finalFuel = 0 := by omega
  have hz : finalFuel = List.replicate h false :=
    ExecCNFTupleEnumeration.word_eq_of_length_value (by simpa using hfl) (by simpa using hzero)
  rw [htotal, hz] at he
  rw [he] at hrun
  rw [CounterForPrograms.budgetSum_const] at hcost
  exact ⟨costs, n, e.regs, hrun, hcost⟩

theorem for_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) :
    ∃ n ≤ candidate.val *
        (bodyBound W (naturalKey W rows h candidate) rows h B + 16 * h + 16) + 8 * h + 8,
      ∃ out, Eval (CounterForPrograms.forCmd countdownPorts body) n
        (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
          (ExecCNFTupleEnumeration.fixedBits h candidate) true [] [])
        (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h candidate)
          (List.replicate h false)
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []) := by
  let a := workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
    (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
    (ExecCNFTupleEnumeration.fixedBits h candidate) true [] []
  let t := CounterForPrograms.testResult countdownPorts a
  have ht : t = workState t.regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
      (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
      (ExecCNFTupleEnumeration.fixedBits h candidate) true [] [] := by
    apply congrArg (StructuredProgram.State.mk t.regs)
    exact CounterForPrograms.testResult_stacks countdownPorts a rfl
  have hf : t.regs 15 = !(CounterPrograms.isZero (ExecCNFTupleEnumeration.fixedBits h candidate)) :=
    CounterForPrograms.testResult_flag countdownPorts a
  obtain ⟨costs, ns, out, hv, hc⟩ := visits_exists W rows h B hlen hwidth candidate candidate.val
    0 (ExecCNFTupleEnumeration.fixedBits h candidate) t.regs (by omega) (by simp)
    (ExecCNFTupleEnumeration.fixedBits_value h candidate candidate.isLt) hf
  simp only [AttainedSignatures.duplicateScan, Bool.not_false] at hv
  rw [← ht] at hv
  have htest := CounterForPrograms.test_eval countdownPorts a (by rfl)
  have hrun := htest.seq hv.eval
  obtain ⟨hcount, _, _, htime⟩ := hv.bounds
  have hlen' : (t.stacks countdownPorts.counter).length = h := by
    rw [ht]
    simp [workState, countdownPorts]
  have hval : CounterPrograms.value (t.stacks countdownPorts.counter) = candidate.val := by
    rw [ht]
    exact ExecCNFTupleEnumeration.fixedBits_value h candidate candidate.isLt
  rw [hval] at hcount
  rw [hlen', hcount] at htime
  refine ⟨_, ?_, out, hrun⟩
  change 8 * (ExecCNFTupleEnumeration.fixedBits h candidate).length + 7 + ns ≤ _
  rw [ExecCNFTupleEnumeration.fixedBits_length]
  nlinarith

/-- All live arrays and all four retained words are included. -/
theorem workState_stackBits (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) :
    stackBits (workState regs W rows candidate saved predecessor fuel fresh [] []).stacks =
      W.length + (words (rows.map words)).length + candidate.length + saved.length +
        predecessor.length + fuel.length + 1 := by
  simp [stackBits, workState, Fin.sum_univ_succ, Nat.add_assoc]

def boundaryBound (W saved : List Bool) (rows : List (List (List Bool))) (h : ℕ) : ℕ :=
  W.length + (words (rows.map words)).length + saved.length + 3 * h + 1

theorem boundary_stackBits (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h c i : ℕ) (fuel : List Bool)
    (hf : fuel.length = h) (fresh : Bool) :
    stackBits (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h c)
      (naturalKey W rows h c) (ExecCNFTupleEnumeration.fixedBits h i) fuel fresh [] []).stacks =
      boundaryBound W (naturalKey W rows h c) rows h := by
  rw [workState_stackBits]
  simp only [ExecCNFTupleEnumeration.fixedBits_length, hf, boundaryBound]
  omega

inductive Boundary (W : List Bool) (rows : List (List (List Bool))) (h c phase : ℕ)
    (a : Data) : Prop where
  | intro (i : ℕ) (fuel : List Bool) (fresh : Bool) (hi : i ≤ c)
      (hv : i + CounterPrograms.value fuel = c + phase) (hl : fuel.length = h)
      (he : a = workState a.regs W rows (ExecCNFTupleEnumeration.fixedBits h c)
        (naturalKey W rows h c) (ExecCNFTupleEnumeration.fixedBits h i) fuel fresh [] []) :
      Boundary W rows h c phase a

theorem Boundary.stackBits {W : List Bool} {rows : List (List (List Bool))}
    {h c phase : ℕ} {a : Data} (ha : Boundary W rows h c phase a) :
    stackBits a.stacks = boundaryBound W (naturalKey W rows h c) rows h := by
  obtain ⟨i, fuel, fresh, _, _, hf, he⟩ := ha
  rw [he]
  exact boundary_stackBits a.regs W rows h c i fuel hf fresh

theorem boundary_after_body (W : List Bool) (rows : List (List (List Bool)))
    (h B : ℕ) (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B) (candidate : Fin (2 ^ h))
    {a b : Data} {n : ℕ} (hb : Eval body n a b)
    (ha : Boundary W rows h candidate 0 a)
    (hp : 0 < CounterPrograms.value (a.stacks countdownPorts.counter)) :
    Boundary W rows h candidate 1 b ∧
      n ≤ bodyBound W (naturalKey W rows h candidate) rows h B := by
  obtain ⟨i, fuel, fresh, hi, hv, hl, he⟩ := ha
  have hp' : 0 < CounterPrograms.value fuel := by
    rw [he] at hp
    exact hp
  have hil : i < 2 ^ h := lt_of_le_of_lt hi candidate.isLt
  have hn : i + 1 < 2 ^ h := by have := candidate.isLt; omega
  obtain ⟨nb, hnb, rb, hb'⟩ := body_eval a.regs W rows
    (ExecCNFTupleEnumeration.fixedBits h candidate) (naturalKey W rows h candidate)
    (ExecCNFTupleEnumeration.fixedBits h i) fuel fresh (by simpa using hlen)
  have hb0 := hb
  rw [he] at hb0
  have hn' := StreamResources.eval_steps_eq 0 0 hb0 hb'
  have hf := hb0.final_unique 0 hb'
  have hw := Counters.increment_word (⟨i, hil⟩ : Fin (2 ^ h)) hn
  constructor
  · refine ⟨i + 1, fuel,
      fresh && !decide (naturalKey W rows h i = naturalKey W rows h candidate),
      by omega, by omega, hl, ?_⟩
    rw [hf]
    exact congrArg (fun w => workState rb W rows
      (ExecCNFTupleEnumeration.fixedBits h candidate) (naturalKey W rows h candidate)
      w fuel (fresh && !decide (naturalKey W rows h i = naturalKey W rows h candidate)) [] []) hw
  · rw [hn']
    exact hnb.trans (bodyCost_le W _ _ rows h B (by simp) hlen hwidth)

theorem boundary_next (W : List Bool) (rows : List (List (List Bool)))
    (h c : ℕ) {a : Data} (ha : Boundary W rows h c 1 a)
    (hp : 0 < CounterPrograms.value (a.stacks countdownPorts.counter)) :
    Boundary W rows h c 0 (CounterForPrograms.nextState countdownPorts a) := by
  obtain ⟨i, fuel, fresh, hi, hv, hl, he⟩ := ha
  have hp' : 0 < CounterPrograms.value fuel := by
    rw [he] at hp
    exact hp
  have hd := CounterPrograms.value_decrement hp'
  refine ⟨i, CounterPrograms.ripple false fuel, fresh, hi, by omega,
    (CounterPrograms.decrement_length hp').trans hl, ?_⟩
  rw [he]
  exact nextState_workState a.regs W rows _ _ _ fuel fresh

/-- The exponential count of visits does not occur in this all-prefix bound. -/
theorem visits_stack_bound (W : List Bool) (rows : List (List (List Bool)))
    (h B : ℕ) (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B) (candidate : Fin (2 ^ h))
    {costs : List ℕ} {n : ℕ} {a b : Data}
    (hv : CounterForPrograms.Visits countdownPorts body costs n a b)
    (ha : Boundary W rows h candidate 0 a) :
    ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (compiled (CounterForPrograms.loopCmd countdownPorts body) 19 19)
        prefixSteps (a.withPC (some (compiled
          (CounterForPrograms.loopCmd countdownPorts body) 19 19).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤
        max (boundaryBound W (naturalKey W rows h candidate) rows h +
          bodyBound W (naturalKey W rows h candidate) rows h B)
          (40 * boundaryBound W (naturalKey W rows h candidate) rows h + 16) := by
  let base := boundaryBound W (naturalKey W rows h candidate) rows h
  let callbackBudget := bodyBound W (naturalKey W rows h candidate) rows h B
  have hbound (phase : ℕ) (a : Data) (ha : Boundary W rows h candidate phase a)
      (i : Fin 24) : (a.stacks i).length ≤ base := by
    have hs := Finset.single_le_sum (fun j _ => Nat.zero_le ((a.stacks j).length))
      (Finset.mem_univ i)
    change (a.stacks i).length ≤ stackBits a.stacks at hs
    rw [ha.stackBits] at hs
    exact hs
  have hcallback : ∀ a b nb, Eval body nb a b → Boundary W rows h candidate 0 a →
      a.regs (countdownPorts.register 2) = true →
      0 < CounterPrograms.value (a.stacks countdownPorts.counter) →
      Boundary W rows h candidate 1 b ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ nb →
        Trace (compiled body 19 19) prefixSteps
          (a.withPC (some (compiled body 19 19).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ base + callbackBudget := by
    intro a b nb hb ha _ hp
    obtain ⟨hfinal, htime⟩ := boundary_after_body W rows h B hlen hwidth candidate hb ha hp
    refine ⟨hfinal, ?_⟩
    intro prefixSteps intermediate hle ht i
    apply StructuredSpace.local_stack_bound (compiled body 19 19)
      (steps := callbackBudget) (initialBound := base) _ prefixSteps intermediate
      (hle.trans htime) ht i
    exact le_of_eq ha.stackBits
  have ht := Enumerators.countdown_visits_stack_bound countdownPorts body
    (Boundary W rows h candidate 0) (Boundary W rows h candidate 1)
    base (base + callbackBudget) (hbound 0) (hbound 1) hcallback
    (fun a ha hp => boundary_next W rows h candidate ha hp) hv ha
  intro prefixSteps intermediate hle htrace i
  have hi := ht prefixSteps intermediate hle htrace i
  exact hi.trans (by dsimp [base, callbackBudget]; omega)

def loopSpace (W : List Bool) (rows : List (List (List Bool))) (h B c : ℕ) : ℕ :=
  max (boundaryBound W (naturalKey W rows h c) rows h +
      bodyBound W (naturalKey W rows h c) rows h B)
    (40 * boundaryBound W (naturalKey W rows h c) rows h + 16)

/-- Every prefix of the actual counted rescan, including test and halt. -/
theorem for_stack_bound (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) {n : ℕ} {finish : Data}
    (heval : Eval (CounterForPrograms.forCmd countdownPorts body) n
      (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
        (ExecCNFTupleEnumeration.fixedBits h candidate) true [] []) finish) :
    ∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
      Trace (compiled (CounterForPrograms.forCmd countdownPorts body) 19 19)
        prefixSteps ((workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
          (ExecCNFTupleEnumeration.fixedBits h candidate) true [] []).withPC
          (some (compiled (CounterForPrograms.forCmd countdownPorts body) 19 19).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ loopSpace W rows h B candidate := by
  let a := workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
    (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
    (ExecCNFTupleEnumeration.fixedBits h candidate) true [] []
  let t := CounterForPrograms.testResult countdownPorts a
  have ht : t = workState t.regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
      (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
      (ExecCNFTupleEnumeration.fixedBits h candidate) true [] [] := by
    apply congrArg (StructuredProgram.State.mk t.regs)
    exact CounterForPrograms.testResult_stacks countdownPorts a rfl
  have hf : t.regs 15 = !(CounterPrograms.isZero (ExecCNFTupleEnumeration.fixedBits h candidate)) :=
    CounterForPrograms.testResult_flag countdownPorts a
  obtain ⟨costs, ns, out, hv, _⟩ := visits_exists W rows h B hlen hwidth candidate candidate.val
    0 (ExecCNFTupleEnumeration.fixedBits h candidate) t.regs (by omega) (by simp)
    (ExecCNFTupleEnumeration.fixedBits_value h candidate candidate.isLt) hf
  simp only [AttainedSignatures.duplicateScan, Bool.not_false] at hv
  rw [← ht] at hv
  have hI : Boundary W rows h candidate 0 t := by
    refine ⟨0, ExecCNFTupleEnumeration.fixedBits h candidate, true, by omega, ?_, by simp, ht⟩
    rw [ExecCNFTupleEnumeration.fixedBits_value h candidate candidate.isLt]
    omega
  have hloop := visits_stack_bound W rows h B hlen hwidth candidate hv hI
  have hinitial : ∀ i, (a.stacks i).length ≤
      boundaryBound W (naturalKey W rows h candidate) rows h := by
    intro i
    have hs := Finset.single_le_sum (fun j _ => Nat.zero_le ((a.stacks j).length))
      (Finset.mem_univ i)
    change (a.stacks i).length ≤ stackBits a.stacks at hs
    have hb := boundary_stackBits regs W rows h candidate 0
      (ExecCNFTupleEnumeration.fixedBits h candidate) (by simp) true
    rw [hb] at hs
    exact hs
  have hb := Enumerators.countdown_for_stack_bound countdownPorts body (by rfl)
    hinitial hv hloop
  have htest := CounterForPrograms.test_eval countdownPorts a (by rfl)
  have hsame := StreamResources.eval_steps_eq 19 19 heval (htest.seq hv.eval)
  intro prefixSteps intermediate hle htrace i
  have hle' : prefixSteps ≤ 8 * (a.stacks countdownPorts.counter).length + 7 + ns + 1 := by
    rw [hsame] at hle
    exact hle
  have hi := hb prefixSteps intermediate hle' htrace i
  exact hi.trans (by unfold loopSpace; omega)

def setup : Code := .seq (copy 16 19) (storeFresh true)

def cleanup : Code := .seq (clear 18) (.call (StackRoutines.transferProgram 19 18 0 1))

/-- The candidate word supplies the binary predecessor count. Its width is h;
the final zero countdown word resets the predecessor without a family table. -/
def command : Code := .seq setup
  (.seq (CounterForPrograms.forCmd countdownPorts body) cleanup)

theorem setup_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor : List Bool) (fresh : Bool) :
    ∃ out, Eval setup (7 * candidate.length + 12)
      (workState regs W rows candidate saved predecessor [] fresh [] [])
      (workState out W rows candidate saved predecessor candidate true [] []) := by
  let a := workState regs W rows candidate saved predecessor [] fresh [] []
  let r₁ := readRegs regs 0 1 none
  have hcopy : Eval (copy 16 19) (7 * candidate.length + 5) a
      (workState r₁ W rows candidate saved predecessor candidate fresh [] []) := by
    have ht := copy_eval 16 19 a (by decide) (by decide) (by decide) rfl
    have he : (⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks 16 19 a.stacks⟩ : Data) =
        workState r₁ W rows candidate saved predecessor candidate fresh [] [] := by
      apply congrArg (StructuredProgram.State.mk r₁)
      funext i
      fin_cases i <;> simp [a, workState, StackRoutines.copyStacks]
    rw [he] at ht
    exact ht
  obtain ⟨r₂, hf⟩ := storeFresh_eval true r₁ W rows candidate saved predecessor candidate fresh [] []
  exact ⟨r₂, by simpa only [setup] using hcopy.seq hf⟩

theorem cleanup_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved : List Bool) (h : ℕ) (answer : Bool) :
    ∃ out, Eval cleanup (2 * candidate.length + 3 * h + 6)
      (workState regs W rows candidate saved candidate (List.replicate h false) answer [] [])
      (workState out W rows candidate saved (List.replicate h false) [] answer [] []) := by
  let r₁ := readRegs regs 0 1 none
  have hclear : Eval (clear 18) (2 * candidate.length + 3)
      (workState regs W rows candidate saved candidate (List.replicate h false) answer [] [])
      (workState r₁ W rows candidate saved [] (List.replicate h false) answer [] []) := by
    have ht := clear_eval 18
      (workState regs W rows candidate saved candidate (List.replicate h false) answer [] [])
    have he : StackRoutines.clearStacks 18
        (workState regs W rows candidate saved candidate (List.replicate h false) answer [] []).stacks =
        (workState r₁ W rows candidate saved [] (List.replicate h false) answer [] []).stacks := by
      funext i
      fin_cases i <;> simp [workState, StackRoutines.clearStacks]
    rw [he] at ht
    exact ht
  let b := workState r₁ W rows candidate saved [] (List.replicate h false) answer [] []
  let r₂ := readRegs r₁ 0 1 none
  have htransfer : Eval (.call (StackRoutines.transferProgram 19 18 0 1)) (3 * h + 3) b
      (workState r₂ W rows candidate saved (List.replicate h false) [] answer [] []) := by
    have ht : Eval (.call (StackRoutines.transferProgram 19 18 0 1))
        (3 * (b.stacks 19).length + 3) b
        ⟨readRegs b.regs 0 1 none, StackRoutines.transferStacks 19 18 b.stacks⟩ :=
      .call _ (ListRegisterProgram.transfer_run (19 : Fin 24) 18
        (0 : Fin 16) 1 (by decide) (by decide) b.regs b.stacks)
    have he : StackRoutines.transferStacks 19 18 b.stacks =
        (workState r₂ W rows candidate saved (List.replicate h false) [] answer [] []).stacks := by
      funext i
      fin_cases i <;> simp [b, workState, StackRoutines.transferStacks]
    rw [he] at ht
    have htarget :
        (⟨readRegs b.regs 0 1 none,
          (workState r₂ W rows candidate saved (List.replicate h false) [] answer [] []).stacks⟩ :
            Data) =
          workState r₂ W rows candidate saved (List.replicate h false) [] answer [] [] := by
      apply congrArg₂ StructuredProgram.State.mk <;> rfl
    rw [htarget] at ht
    change Eval (.call (StackRoutines.transferProgram 19 18 0 1))
      (3 * (List.replicate h false).length + 3) b _ at ht
    simpa only [List.length_replicate] using ht
  refine ⟨r₂, ?_⟩
  convert hclear.seq htransfer using 1
  · rfl
  · omega

theorem command_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (fresh : Bool) :
    ∃ n ≤ candidate.val *
        (bodyBound W (naturalKey W rows h candidate) rows h B + 16 * h + 16) + 20 * h + 26,
      ∃ out, Eval command n
        (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
          [] fresh [] [])
        (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (List.replicate h false) []
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []) := by
  obtain ⟨r₁, hs⟩ := setup_eval regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
    (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0) fresh
  obtain ⟨nf, hnf, rf, hf⟩ := for_eval r₁ W rows h B hlen hwidth candidate
  obtain ⟨r₂, hc⟩ := cleanup_eval rf W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
    (naturalKey W rows h candidate) h
    (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate))
  refine ⟨_, ?_, r₂, hs.seq (hf.seq hc)⟩
  simp only [ExecCNFTupleEnumeration.fixedBits_length]
  omega

theorem sequence_stack_bound {first second : Code} {n m bound : ℕ} {a b c : Data}
    (hf : Eval first n a b) (hs : Eval second m b c)
    (hfirst : ∀ p q, p ≤ n → Trace (compiled first 19 19) p
      (a.withPC (some (compiled first 19 19).entry)) q → ∀ i, (q.stacks i).length ≤ bound)
    (hsecond : ∀ p q, p ≤ m → Trace (compiled second 19 19) p
      (b.withPC (some (compiled second 19 19).entry)) q → ∀ i, (q.stacks i).length ≤ bound) :
    ∀ p q, p ≤ n + m → Trace (compiled (.seq first second) 19 19) p
      (a.withPC (some (compiled (.seq first second) 19 19).entry)) q →
      ∀ i, (q.stacks i).length ≤ bound :=
  StructuredSpace.sequence_stack_bound hf hs 19 19 hfirst hsecond
    (compiled (.seq first second) 19 19) (siteAddress _) (exitAddress _)
    (compiled_site _ 19 19)

theorem control_space_le (W : List Bool) (rows : List (List (List Bool))) (h B c t : ℕ)
    (ht : t ≤ 7 * h + 12) :
    boundaryBound W (naturalKey W rows h c) rows h + t ≤ loopSpace W rows h B c := by
  unfold loopSpace boundaryBound
  omega

theorem command_stack_bound (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (fresh : Bool) {n : ℕ} {finish : Data}
    (heval : Eval command n
      (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
        [] fresh [] []) finish) :
    ∀ p q, p ≤ n + 1 → Trace (compiled command 19 19) p
      ((workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
        [] fresh [] []).withPC (some (compiled command 19 19).entry)) q →
      ∀ i, (q.stacks i).length ≤ loopSpace W rows h B candidate := by
  obtain ⟨r₁, hs⟩ := setup_eval regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
    (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0) fresh
  obtain ⟨nf, _, rf, hf⟩ := for_eval r₁ W rows h B hlen hwidth candidate
  obtain ⟨r₂, hc⟩ := cleanup_eval rf W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
    (naturalKey W rows h candidate) h
    (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate))
  simp only [ExecCNFTupleEnumeration.fixedBits_length] at hs hc
  let base := boundaryBound W (naturalKey W rows h candidate) rows h
  have hsetup : ∀ p q, p ≤ 7 * h + 12 → Trace (compiled setup 19 19) p
      ((workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
        [] fresh [] []).withPC (some (compiled setup 19 19).entry)) q →
      ∀ i, (q.stacks i).length ≤ loopSpace W rows h B candidate := by
    intro p q hp hq i
    have hb : stackBits (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
        [] fresh [] []).stacks ≤ base := by
      rw [workState_stackBits]
      simp only [ExecCNFTupleEnumeration.fixedBits_length, List.length_nil]
      dsimp [base, boundaryBound]
      omega
    have hh := StructuredSpace.local_stack_bound (compiled setup 19 19)
      (a := (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
        [] fresh [] []).withPC (some (compiled setup 19 19).entry))
      (steps := 7 * h + 12) hb p q hp hq i
    exact hh.trans (control_space_le W rows h B candidate _ le_rfl)
  have hcleanup : ∀ p q, p ≤ 5 * h + 6 → Trace (compiled cleanup 19 19) p
      ((workState rf W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h candidate)
        (List.replicate h false)
        (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []).withPC
        (some (compiled cleanup 19 19).entry)) q →
      ∀ i, (q.stacks i).length ≤ loopSpace W rows h B candidate := by
    intro p q hp hq i
    have hb := boundary_stackBits rf W rows h candidate candidate
      (List.replicate h false) (by simp)
      (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate))
    have hh := StructuredSpace.local_stack_bound (compiled cleanup 19 19)
      (a := (workState rf W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h candidate)
        (List.replicate h false)
        (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []).withPC
        (some (compiled cleanup 19 19).entry))
      (steps := 5 * h + 6) (le_of_eq hb) p q hp hq i
    exact hh.trans (control_space_le W rows h B candidate _ (by omega))
  have hloop := for_stack_bound r₁ W rows h B hlen hwidth candidate hf
  have hcleanupCost : 2 * h + 3 * h + 6 = 5 * h + 6 := by omega
  rw [hcleanupCost] at hc
  have htail := sequence_stack_bound hf hc
    (fun p q hp hq i => hloop p q (by omega) hq i) hcleanup
  have hwhole := sequence_stack_bound hs (hf.seq hc) hsetup htail
  have hhalt := StructuredSpace.compiled_halt_stack_bound (hs.seq (hf.seq hc)) 19 19 hwhole
  have htime := StreamResources.eval_steps_eq 19 19 heval (hs.seq (hf.seq hc))
  intro p q hp hq i
  rw [htime] at hp
  exact hhalt p q hp hq i

/-- Compute the candidate's whole key once and retain it through the rescan. -/
def prepareKey : Code := .seq (copy 16 12) (.seq keyCall
  (.seq (copy 14 17) (.seq (clear 12) (clear 14))))

theorem prepareKey_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate predecessor : List Bool) (fresh : Bool)
    (hlen : ∀ row ∈ rows, row.length = candidate.length) :
    ∃ n ≤ cost W candidate rows + 9 * candidate.length +
        9 * (signatureValue W candidate rows).length + 17, ∃ out,
      Eval prepareKey n (workState regs W rows candidate [] predecessor [] fresh [] [])
        (workState out W rows candidate (signatureValue W candidate rows)
          predecessor [] fresh [] []) := by
  let a := workState regs W rows candidate [] predecessor [] fresh [] []
  let r₁ := readRegs regs 0 1 none
  have hcopy : Eval (copy 16 12) (7 * candidate.length + 5) a
      (workState r₁ W rows candidate [] predecessor [] fresh candidate []) := by
    have ht := copy_eval 16 12 a (by decide) (by decide) (by decide) rfl
    have he : (⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks 16 12 a.stacks⟩ : Data) =
        workState r₁ W rows candidate [] predecessor [] fresh candidate [] := by
      apply congrArg (StructuredProgram.State.mk r₁)
      funext i
      fin_cases i <;> simp [a, workState, StackRoutines.copyStacks]
    rw [he] at ht
    exact ht
  obtain ⟨nk, hnk, rk, hk⟩ := keyCall_eval r₁ W rows candidate [] predecessor []
    fresh candidate [] hlen
  simp only [List.append_nil] at hk
  let key := signatureValue W candidate rows
  let r₂ := readRegs rk 0 1 none
  have hsave : Eval (copy 14 17) (7 * key.length + 5)
      (workState rk W rows candidate [] predecessor [] fresh candidate key)
      (workState r₂ W rows candidate key predecessor [] fresh candidate key) := by
    have ht := copy_eval 14 17
      (workState rk W rows candidate [] predecessor [] fresh candidate key)
      (by decide) (by decide) (by decide) rfl
    have he : StackRoutines.copyStacks 14 17
        (workState rk W rows candidate [] predecessor [] fresh candidate key).stacks =
        (workState r₂ W rows candidate key predecessor [] fresh candidate key).stacks := by
      funext i
      fin_cases i <;> simp [workState, StackRoutines.copyStacks]
    rw [he] at ht
    exact ht
  let r₃ := readRegs r₂ 0 1 none
  have hbits : Eval (clear 12) (2 * candidate.length + 3)
      (workState r₂ W rows candidate key predecessor [] fresh candidate key)
      (workState r₃ W rows candidate key predecessor [] fresh [] key) := by
    have ht := clear_eval 12 (workState r₂ W rows candidate key predecessor [] fresh candidate key)
    have he : StackRoutines.clearStacks 12
        (workState r₂ W rows candidate key predecessor [] fresh candidate key).stacks =
        (workState r₃ W rows candidate key predecessor [] fresh [] key).stacks := by
      funext i
      fin_cases i <;> simp [workState, StackRoutines.clearStacks]
    rw [he] at ht
    exact ht
  let r₄ := readRegs r₃ 0 1 none
  have hkey : Eval (clear 14) (2 * key.length + 3)
      (workState r₃ W rows candidate key predecessor [] fresh [] key)
      (workState r₄ W rows candidate key predecessor [] fresh [] []) := by
    have ht := clear_eval 14 (workState r₃ W rows candidate key predecessor [] fresh [] key)
    have he : StackRoutines.clearStacks 14
        (workState r₃ W rows candidate key predecessor [] fresh [] key).stacks =
        (workState r₄ W rows candidate key predecessor [] fresh [] []).stacks := by
      funext i
      fin_cases i <;> simp [workState, StackRoutines.clearStacks]
    rw [he] at ht
    exact ht
  refine ⟨_, ?_, r₄, hcopy.seq (hk.seq (hsave.seq (hbits.seq hkey)))⟩
  dsimp [key] at *
  omega

def candidateCommand : Code := .seq prepareKey command

theorem candidateCommand_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (fresh : Bool) :
    ∃ n ≤ cost W (ExecCNFTupleEnumeration.fixedBits h candidate) rows +
        9 * (naturalKey W rows h candidate).length +
        candidate.val * (bodyBound W (naturalKey W rows h candidate) rows h B + 16 * h + 16) +
        29 * h + 43, ∃ out,
      Eval candidateCommand n
        (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
          (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] [])
        (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (List.replicate h false) []
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []) := by
  obtain ⟨np, hnp, rp, hp⟩ := prepareKey_eval regs W rows
    (ExecCNFTupleEnumeration.fixedBits h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
    fresh (by simpa using hlen)
  obtain ⟨nc, hnc, rc, hc⟩ := command_eval rp W rows h B hlen hwidth candidate fresh
  refine ⟨np + nc, ?_, rc, hp.seq hc⟩
  simp only [ExecCNFTupleEnumeration.fixedBits_length] at hnp
  change np ≤ cost W (ExecCNFTupleEnumeration.fixedBits h candidate) rows +
    9 * h + 9 * (naturalKey W rows h candidate).length + 17 at hnp
  omega

def candidateProgram := compiled candidateCommand 16 22

theorem candidate_stack_bound (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (fresh : Bool) {n : ℕ} {finish : Data}
    (heval : Eval candidateCommand n
      (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
        (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] []) finish) :
    ∀ p q, p ≤ n + 1 → Trace candidateProgram p
      ((workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
        (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] []).withPC
        (some candidateProgram.entry)) q →
      ∀ i, (q.stacks i).length ≤ loopSpace W rows h B candidate := by
  obtain ⟨np, hnp, rp, hp⟩ := prepareKey_eval regs W rows
    (ExecCNFTupleEnumeration.fixedBits h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
    fresh (by simpa using hlen)
  obtain ⟨nc, _, rc, hc⟩ := command_eval rp W rows h B hlen hwidth candidate fresh
  let base := boundaryBound W (naturalKey W rows h candidate) rows h
  have htime : np ≤ bodyBound W (naturalKey W rows h candidate) rows h B := by
    have hs := cost_le W (ExecCNFTupleEnumeration.fixedBits h candidate) rows B
      (by simpa using hlen) hwidth
    simp only [ExecCNFTupleEnumeration.fixedBits_length] at hs hnp
    unfold bodyBound naturalKey
    omega
  have hprepare : ∀ p q, p ≤ np → Trace (compiled prepareKey 19 19) p
      ((workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
        (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] []).withPC
        (some (compiled prepareKey 19 19).entry)) q →
      ∀ i, (q.stacks i).length ≤ loopSpace W rows h B candidate := by
    intro p q hp' hq i
    have hb : stackBits (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
        (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] []).stacks ≤ base := by
      rw [workState_stackBits]
      simp only [ExecCNFTupleEnumeration.fixedBits_length, List.length_nil]
      dsimp [base, boundaryBound]
      omega
    have hh := StructuredSpace.local_stack_bound (compiled prepareKey 19 19)
      (a := (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
        (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] []).withPC
        (some (compiled prepareKey 19 19).entry))
      (steps := bodyBound W (naturalKey W rows h candidate) rows h B)
      hb p q (hp'.trans htime) hq i
    exact hh.trans (Nat.le_max_left _ _)
  have hscan := command_stack_bound rp W rows h B hlen hwidth candidate fresh hc
  have hwhole := sequence_stack_bound hp hc hprepare
    (fun p q hp' hq i => hscan p q (by omega) hq i)
  have hconverted := StructuredSpace.command_stack_bound (hp.seq hc) 19 19 hwhole
    candidateProgram (siteAddress candidateCommand) (exitAddress candidateCommand)
    (compiled_site candidateCommand 16 22)
  have hhalt := StructuredSpace.compiled_halt_stack_bound (hp.seq hc) 16 22 hconverted
  have hn := StreamResources.eval_steps_eq 16 22 heval (hp.seq hc)
  intro p q hp' hq i
  rw [hn] at hp'
  exact hhalt p q hp' hq i

theorem naturalKey_eq_iff {h d : ℕ} (W : List Bool)
    (c : Fin d → Fin h → List Bool) (A : Fin d → Fin h → ℤ)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) + A j i) (i j : Fin (2 ^ h)) :
    naturalKey W (List.ofFn (fun row => List.ofFn (c row))) h i =
      naturalKey W (List.ofFn (fun row => List.ofFn (c row))) h j ↔
      AttainedSignatures.integerKey A i = AttainedSignatures.integerKey A j := by
  unfold naturalKey
  rw [← AttainedSignatures.assignment_word h i, ← AttainedSignatures.assignment_word h j]
  exact key_eq_iff W c A _ _ hc

/-- Lexicographic comparison with coordinate priority h−1,...,0: compare
higher coordinates first, and use the low bit only when their tails agree. -/
inductive ReverseLex : List Bool → List Bool → Prop where
  | higher {a b : Bool} {xs ys : List Bool} (h : ReverseLex xs ys) :
      ReverseLex (a :: xs) (b :: ys)
  | low (xs : List Bool) : ReverseLex (false :: xs) (true :: xs)

theorem reverseLex_iff_value_lt (xs ys : List Bool) (hlen : xs.length = ys.length) :
    ReverseLex xs ys ↔ CounterPrograms.value xs < CounterPrograms.value ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => constructor <;> intro h <;> cases h
    | cons b ys => simp at hlen
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      have hl : xs.length = ys.length := by simpa using hlen
      constructor
      · intro h
        cases h with
        | higher h =>
          have hv := (ih ys hl).mp h
          cases a <;> cases b <;> simp only [CounterPrograms.value, Bool.toNat_false, Bool.toNat_true] <;> omega
        | low => simp [CounterPrograms.value]
      · intro hv
        by_cases ht : CounterPrograms.value xs < CounterPrograms.value ys
        · exact .higher ((ih ys hl).mpr ht)
        have he : CounterPrograms.value xs = CounterPrograms.value ys := by
          cases a <;> cases b <;> simp only [CounterPrograms.value, Bool.toNat_false, Bool.toNat_true] at hv <;> omega
        have hw := ExecCNFTupleEnumeration.word_eq_of_length_value hl he
        subst ys
        cases a <;> cases b
        · simp [CounterPrograms.value] at hv
        · exact .low xs
        · simp [CounterPrograms.value] at hv
        · simp [CounterPrograms.value] at hv

theorem fixedBits_lex_iff (h : ℕ) (i j : Fin (2 ^ h)) :
    ReverseLex (ExecCNFTupleEnumeration.fixedBits h i)
      (ExecCNFTupleEnumeration.fixedBits h j) ↔ i < j := by
  rw [reverseLex_iff_value_lt _ _ (by simp),
    ExecCNFTupleEnumeration.fixedBits_value h i i.isLt,
    ExecCNFTupleEnumeration.fixedBits_value h j j.isLt]
  rfl

theorem actual_increment_lex (h : ℕ) (i : Fin (2 ^ h)) (hi : i.val + 1 < 2 ^ h) :
    ReverseLex (ExecCNFTupleEnumeration.fixedBits h i)
      (CounterPrograms.ripple true (ExecCNFTupleEnumeration.fixedBits h i)) := by
  have hw : CounterPrograms.ripple true (ExecCNFTupleEnumeration.fixedBits h i) =
      ExecCNFTupleEnumeration.fixedBits h (i.val + 1) := Counters.increment_word i hi
  rw [hw]
  exact (fixedBits_lex_iff h i ⟨i.val + 1, hi⟩).mpr (show i.val < i.val + 1 from Nat.lt_succ_self _)

/-- A uniform polynomial local budget, before the exponential scan counts. -/
def polynomialBudget (W : List Bool) (rows : List (List (List Bool))) (h B : ℕ) : ℕ :=
  14 * (words (rows.map words)).length +
    2 * (rows.length * (signatureRowBound W h B + 2)) +
    38 * keyBound W h rows.length B + 62 * h + 129

theorem naturalKey_length_le (W : List Bool) (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B) (c : ℕ) :
    (naturalKey W rows h c).length ≤ keyBound W h rows.length B := by
  have ht := signatureValue_length_bound W (ExecCNFTupleEnumeration.fixedBits h c) rows B
    (by simpa using hlen) hwidth
  simpa only [naturalKey, keyBound,
    ExecCNFTupleEnumeration.fixedBits_length] using ht

theorem candidate_time_uniform (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (fresh : Bool) :
    ∃ n ≤ (candidate.val + 1) * polynomialBudget W rows h B, ∃ out,
      Eval candidateCommand n
        (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
          (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] [])
        (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (List.replicate h false) []
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []) := by
  obtain ⟨n, hn, out, ht⟩ := candidateCommand_eval regs W rows h B hlen hwidth candidate fresh
  have hs := cost_le W (ExecCNFTupleEnumeration.fixedBits h candidate) rows B
    (by simpa using hlen) hwidth
  simp only [ExecCNFTupleEnumeration.fixedBits_length] at hs
  have hk := naturalKey_length_le W rows h B hlen hwidth candidate
  have hbody : bodyBound W (naturalKey W rows h candidate) rows h B + 16 * h + 16 ≤
      polynomialBudget W rows h B := by unfold bodyBound polynomialBudget; omega
  have hsetup : cost W (ExecCNFTupleEnumeration.fixedBits h candidate) rows +
      9 * (naturalKey W rows h candidate).length + 29 * h + 43 ≤
      polynomialBudget W rows h B := by unfold polynomialBudget; omega
  refine ⟨n, ?_, out, ht⟩
  calc
    n ≤ candidate.val * polynomialBudget W rows h B + polynomialBudget W rows h B := by
      have hm := Nat.mul_le_mul_left candidate.val hbody
      omega
    _ = (candidate.val + 1) * polynomialBudget W rows h B := by rw [Nat.add_mul, one_mul]

theorem complete_candidate_budget (W : List Bool) (rows : List (List (List Bool))) (h B : ℕ) :
    (∑ candidate : Fin (2 ^ h),
      (candidate.val + 1) * polynomialBudget W rows h B) ≤
      polynomialBudget W rows h B * 4 ^ h := by
  calc
    _ ≤ ∑ _candidate : Fin (2 ^ h), (2 ^ h) * polynomialBudget W rows h B := by
      exact Finset.sum_le_sum (fun candidate _ => Nat.mul_le_mul_right _ (by omega))
    _ = polynomialBudget W rows h B * 4 ^ h := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      rw [← Nat.mul_assoc, ← mul_pow]
      ring

def spaceBudget (W : List Bool) (rows : List (List (List Bool))) (h B : ℕ) : ℕ :=
  40 * (W.length + (words (rows.map words)).length + keyBound W h rows.length B + 3 * h + 1) +
    polynomialBudget W rows h B + 16

theorem loopSpace_le (W : List Bool) (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B) (c : ℕ) :
    loopSpace W rows h B c ≤ spaceBudget W rows h B := by
  have hk := naturalKey_length_le W rows h B hlen hwidth c
  have hb : bodyBound W (naturalKey W rows h c) rows h B ≤ polynomialBudget W rows h B := by
    unfold bodyBound polynomialBudget
    omega
  unfold loopSpace spaceBudget boundaryBound
  omega

/-- One fixed actual candidate machine returns the canonical full key and
freshness bit, with time and every-prefix storage bounds on that same run. -/
theorem candidate_run (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (fresh : Bool) :
    ∃ n ≤ (candidate.val + 1) * polynomialBudget W rows h B + 1, ∃ out,
      Trace candidateProgram n
        ((workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
          (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] []).withPC
          (some candidateProgram.entry))
        ((workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (List.replicate h false) []
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace candidateProgram prefixSteps
          ((workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
            (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] []).withPC
            (some candidateProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ spaceBudget W rows h B := by
  obtain ⟨steps, hsteps, out, he⟩ := candidate_time_uniform regs W rows h B hlen hwidth candidate fresh
  refine ⟨steps + 1, Nat.add_le_add_right hsteps 1, out, compiled_halt_trace he 16 22, ?_⟩
  intro prefixSteps intermediate hle ht i
  exact (candidate_stack_bound regs W rows h B hlen hwidth candidate fresh he
    prefixSteps intermediate hle ht i).trans (loopSpace_le W rows h B hlen hwidth candidate)

/-- Include each concrete compiled invocation's halt in the full generator
charge; no emitted-key count multiplies the raw candidate scan. -/
theorem complete_candidate_run_budget (W : List Bool) (rows : List (List (List Bool)))
    (h B : ℕ) :
    (∑ candidate : Fin (2 ^ h),
      ((candidate.val + 1) * polynomialBudget W rows h B + 1)) ≤
      (polynomialBudget W rows h B + 1) * 4 ^ h := by
  calc
    _ ≤ ∑ _candidate : Fin (2 ^ h), (2 ^ h) * (polynomialBudget W rows h B + 1) := by
      apply Finset.sum_le_sum
      intro candidate _
      have hi : candidate.val + 1 ≤ 2 ^ h := by have := candidate.isLt; omega
      have hm := Nat.mul_le_mul_right (polynomialBudget W rows h B) hi
      have hp : 1 ≤ 2 ^ h := Nat.one_le_pow' h 1
      nlinarith
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      rw [← Nat.mul_assoc, ← mul_pow]
      ring

/-- Both concrete resource expressions have one fixed degree, independent of
head width, matrix dimensions, coefficient values and the candidate cursor. -/
theorem budgets_le_monomial (W : List Bool) (rows : List (List (List Bool))) (h B S : ℕ)
    (hS : 1 ≤ S) (hW : W.length ≤ S) (hd : rows.length ≤ S) (hh : h ≤ S)
    (hB : B ≤ S) (hM : (words (rows.map words)).length ≤ S) :
    polynomialBudget W rows h B ≤ 100000 * S ^ 6 ∧
      spaceBudget W rows h B ≤ 100000 * S ^ 6 := by
  let width := 1 + S * (S + 1 + S)
  let row := (S + 1) * (200 * (width + 2) ^ 2 + 34) + 9 * width + 22
  let signature := 9 * (S * (2 * S + 1)) + 7 + (7 * S + 5) + 2 +
    (row + 1) + 8 * (width + 1) + 8
  let key := S * (2 * (width + 1) + 1)
  let total := 14 * S + 2 * (S * (signature + 2)) + 38 * key + 62 * S + 129
  have hp : polynomialBudget W rows h B ≤ total := by
    dsimp [polynomialBudget, keyBound, signatureRowBound, rowCostBound, widthBound,
      total, signature, row, key, width]
    gcongr
  have hk : keyBound W h rows.length B ≤ key := by
    dsimp [keyBound, widthBound, key, width]
    gcongr
  have hs : spaceBudget W rows h B ≤ 40 * (S + S + key + 3 * S + 1) + total + 16 := by
    unfold spaceBudget
    gcongr
  have h0 : 1 ≤ S ^ 6 := one_le_pow₀ hS
  have h1 : S ≤ S ^ 6 := Nat.le_self_pow (by decide) _
  have h2 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS (by decide)
  have h3 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS (by decide)
  have h4 : S ^ 4 ≤ S ^ 6 := Nat.pow_le_pow_right hS (by decide)
  have h5 : S ^ 5 ≤ S ^ 6 := Nat.pow_le_pow_right hS (by decide)
  dsimp [total, signature, row, key, width] at hp hs
  constructor <;> nlinarith


end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
