import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCoefficientInputs
import OAI.Algorithms.SubexponentialSAT.SubexpCoefficientEntries
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientSearchService
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-! Binary-parameter entry to the concrete normalized-coefficient search. -/

namespace SubexponentialSAT.SubexpCoefficientServiceProgram

open BitProgram StructuredCalls SubexpSetupStorage SubexpSetupBoundSpec
open SubexpCoefficientStaging
open Subexp

abbrev service : Stage where
  registers := 14
  stackCount := 32
  labels := size CoefficientSearchService.command + 1
  program := CoefficientSearchService.program
  register_le := by decide
  stack_le := by decide
  inputs := [(45, 14), (46, 16), (47, 31)]
  inputs_length := by decide
  inputs_nodup := by decide
  source_high := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> decide
  target_low := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> decide
  output := 21
  destination := 48
  destination_high := by decide

theorem service_entry (p A R : ℕ) (a : Data)
    (hp : a.stacks 45 = SubexpAlphabetProgram.primeWord p)
    (hr : a.stacks 46 = List.replicate R true)
    (hA : a.stacks 47 = List.replicate A true) :
    project service.register service.stack (service.prepared a) =
      CoefficientSearchSetup.rawInput p A R ((service.prepared a).regs ∘ service.register) := by
  apply service.project_eq a
  · intro i
    rfl
  · intro q hq j hj
    change q ∈ [(45, 14), (46, 16), (47, 31)] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · have hj' : j = (14 : Fin 32) := Fin.ext (congrArg (fun i : Fin 64 => i.val) hj)
      subst j
      exact hp.symm
    · have hj' : j = (16 : Fin 32) := Fin.ext (congrArg (fun i : Fin 64 => i.val) hj)
      subst j
      exact hr.symm
    · have hj' : j = (31 : Fin 32) := Fin.ext (congrArg (fun i : Fin 64 => i.val) hj)
      subst j
      exact hA.symm
  · intro j hj
    have h14 : j ≠ (14 : Fin 32) := by
      intro h
      subst j
      exact hj (45, 14) (by change (45, 14) ∈ [(45, 14), (46, 16), (47, 31)]; simp) rfl
    have h16 : j ≠ (16 : Fin 32) := by
      intro h
      subst j
      exact hj (46, 16) (by change (46, 16) ∈ [(45, 14), (46, 16), (47, 31)]; simp) rfl
    have h31 : j ≠ (31 : Fin 32) := by
      intro h
      subst j
      exact hj (47, 31) (by change (47, 31) ∈ [(45, 14), (46, 16), (47, 31)]; simp) rfl
    simp only [CoefficientSearchSetup.rawInput, ite_eq_right h14, ite_eq_right h16, ite_eq_right h31]

theorem service_run (p A R B : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) (a : Data) (ha : WordBound B a)
    (hp : a.stacks 45 = SubexpAlphabetProgram.primeWord p)
    (hr : a.stacks 46 = List.replicate R true)
    (hA : a.stacks 47 = List.replicate A true) :
    ∃ (t : ℕ) (b : Data) (v : Fin R → ZMod p), Eval service.command t a b ∧
      t ≤ 400 * (B + CoefficientSearchService.budget p A R + 1) ∧
      WordBound (B + CoefficientSearchService.budget p A R) b ∧
      b.stacks 48 = CoefficientSearchSemantics.encode p v ∧
      CoefficientNormalization.unnormalize (List.ofFn v) = CoefficientSearch.coefficientsNat p A R ∧
      (∀ i : Fin 64, 32 ≤ i.val → i ≠ 63 → i ≠ 48 → b.stacks i = a.stacks i) := by
  obtain ⟨out, v, he, hv, hc⟩ := CoefficientSearchService.program_coefficients p h2 A R
    ((service.prepared a).regs ∘ service.register)
  rw [← service_entry p A R a hp hr hA] at he
  obtain ⟨t, ht, htime, hw⟩ := service.run a out B (CoefficientSearchService.budget p A R) ha he
  exact ⟨t, service.result a out, v, ht, htime, hw,
    (service.result_output a out).trans hv, hc,
    fun i hi h63 h48 => service.result_frame a out i hi h63 h48⟩

def retained (i : Fin 64) : Prop := 40 ≤ i.val ∧ i.val ≤ 44 ∨ i = 48
instance (i : Fin 64) : Decidable (retained i) := inferInstanceAs (Decidable (_ ∨ _))
def cleanupPorts : List (Fin 64) := (List.finRange 64).filter (fun i => !decide (retained i))
def cleanup : Code := .seq (clearMany cleanupPorts) RegisterResetProgram.all
def cleaned (a : Data) : Data := RegisterResetProgram.zeroed (clearManyState cleanupPorts a)
def cleanupCost (a : Data) : ℕ := clearManyCost cleanupPorts a + 16

@[simp] theorem mem_cleanupPorts (i : Fin 64) : i ∈ cleanupPorts ↔ ¬ retained i := by
  simp [cleanupPorts]

theorem cleaned_word (a : Data) (i : Fin 64) :
    (cleaned a).stacks i = if retained i then a.stacks i else [] := by
  simp only [cleaned, RegisterResetProgram.zeroed, clearMany_stacks, mem_cleanupPorts]
  split_ifs <;> simp_all

theorem cleanup_run (B : ℕ) (a : Data) (ha : WordBound B a) :
    Eval cleanup (cleanupCost a) a (cleaned a) ∧
      cleanupCost a ≤ 64 * (2 * B + 3) + 16 ∧ WordBound B (cleaned a) := by
  have hc := clearManyCost_le cleanupPorts a B ha
  have hl : cleanupPorts.length ≤ 64 := by
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n := 64))
  have hmul := Nat.mul_le_mul_right (2 * B + 3) hl
  refine ⟨(clearMany_eval cleanupPorts a).seq (RegisterResetProgram.all_eval _), ?_, ?_⟩
  · unfold cleanupCost
    omega
  · exact clearMany_wordBound cleanupPorts a B ha

def command : Code := .seq SubexpCoefficientInputs.command (.seq service.command cleanup)
def program := compiled command 40 48

def wordBound (p A R B : ℕ) [Fact p.Prime] : ℕ :=
  B + SubexpCoefficientInputs.innerBound B A R + CoefficientSearchService.budget p A R

def budget (p A R B : ℕ) [Fact p.Prime] : ℕ :=
  SubexpCoefficientInputs.budget B A R +
  400 * (wordBound p A R B + 1) + 64 * (2 * wordBound p A R B + 3) + 17

theorem command_run (p A R B : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) (a : Data) (ha : WordBound B a)
    (hp : CounterPrograms.value (a.stacks 40) = p)
    (hr : CounterPrograms.value (a.stacks 43) = R)
    (hA : CounterPrograms.value (a.stacks 44) = A) :
    ∃ (t : ℕ) (b : Data) (v : Fin R → ZMod p), Eval command t a b ∧ t + 1 ≤ budget p A R B ∧
      WordBound (wordBound p A R B) b ∧
      b.stacks 48 = CoefficientSearchSemantics.encode p v ∧
      CoefficientNormalization.unnormalize (List.ofFn v) = CoefficientSearch.coefficientsNat p A R ∧
      (∀ i : Fin 64, 40 ≤ i.val → i.val ≤ 44 → b.stacks i = a.stacks i) ∧
      (∀ i : Fin 64, ¬ retained i → b.stacks i = []) ∧ (∀ i, b.regs i = false) := by
  obtain ⟨ti, i, ei, hti, hwi, hi45, hi46, hi47, hif⟩ :=
    SubexpCoefficientInputs.command_run p A R B a ha hp (Fact.out : p.Prime).pos hr hA
  obtain ⟨ts, s, v, es, hts, hws, hs48, hv, hsf⟩ :=
    service_run p A R _ h2 i hwi hi45 hi46 hi47
  obtain ⟨ec, htc, hwc⟩ := cleanup_run (wordBound p A R B) s hws
  refine ⟨ti + (ts + cleanupCost s), cleaned s, v, ei.seq (es.seq ec), ?_, hwc, ?_, hv,
    ?_, ?_, fun _ => rfl⟩
  · unfold budget wordBound
    unfold wordBound at htc
    omega
  · rw [cleaned_word, ite_eq_left (by right; rfl)]
    exact hs48
  · intro j hj40 hj44
    have hj63 : j ≠ 63 := by intro h; have := congrArg Fin.val h; norm_num at this; omega
    have hj45 : j ≠ 45 := by intro h; have := congrArg Fin.val h; norm_num at this; omega
    have hj46 : j ≠ 46 := by intro h; have := congrArg Fin.val h; norm_num at this; omega
    have hj47 : j ≠ 47 := by intro h; have := congrArg Fin.val h; norm_num at this; omega
    have hj48 : j ≠ 48 := by intro h; have := congrArg Fin.val h; norm_num at this; omega
    rw [cleaned_word, ite_eq_left (show retained j from Or.inl ⟨hj40, hj44⟩)]
    exact (hsf j (by omega) hj63 hj48).trans (hif j (by omega) hj63 hj45 hj46 hj47)
  · intro j hj
    rw [cleaned_word, ite_eq_right hj]

theorem program_run (p A R B : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) (a : Data) (ha : WordBound B a)
    (hp : CounterPrograms.value (a.stacks 40) = p)
    (hr : CounterPrograms.value (a.stacks 43) = R)
    (hA : CounterPrograms.value (a.stacks 44) = A) :
    ∃ (b : Data) (v : Fin R → ZMod p),
      RunsIn program (budget p A R B) (a.withPC (some program.entry)) (b.withPC none) ∧
      b.stacks 48 = CoefficientSearchSemantics.encode p v ∧
      CoefficientNormalization.unnormalize (List.ofFn v) = CoefficientSearch.coefficientsNat p A R ∧
      WordBound (wordBound p A R B) b ∧
      (∀ i : Fin 64, 40 ≤ i.val → i.val ≤ 44 → b.stacks i = a.stacks i) ∧
      (∀ i : Fin 64, ¬ retained i → b.stacks i = []) ∧ (∀ i, b.regs i = false) := by
  obtain ⟨t, b, v, he, ht, hw, ho, hv, hf, hc, hr⟩ := command_run p A R B h2 a ha hp hr hA
  exact ⟨b, v, ⟨t + 1, ht, compiled_halt_trace he 40 48⟩, ho, hv, hw, hf, hc, hr⟩

end SubexponentialSAT.SubexpCoefficientServiceProgram

end OAI.Algorithms
