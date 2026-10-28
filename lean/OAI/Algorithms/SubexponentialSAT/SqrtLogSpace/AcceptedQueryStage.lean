import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

/-! The accepted query physically receives the saved history, without a trial
candidate prefix. All routing, scratch reset and source reclamation are paid
commands. The query is composed through its actual evaluation and prefix proof. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage

open BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.SqrtLog LeafOuterProgram

/-- Reset the routing temporary by an actual finite program. -/
def clearTemporary : Cmd 40 896 := .call (clearProgram 767 0 1)

def temporaryCleared (a : State 40 896) : State 40 896 :=
  ⟨readRegs a.regs 0 1 none, clearStacks 767 a.stacks⟩

def stage : Cmd 40 896 := .seq clearTemporary LeafOuterNative.stageFinal

def staged (a : State 40 896) : State 40 896 :=
  LeafOuterNative.finalStaged (temporaryCleared a)

def stageCost (a : State 40 896) : ℕ :=
  2 * (a.stacks 767).length + 3 + LeafOuterNative.stageFinalCost (temporaryCleared a)

/-- Reuse the six-port reclamation shared with the marked mass adapter. -/
def cleanup : Cmd 40 896 := .seq clearTemporary HashMassStaged.cleanup

def cleaned (a : State 40 896) : State 40 896 :=
  HashMassStaged.cleaned (temporaryCleared a)

def cleanupCost (a : State 40 896) : ℕ :=
  2 * (a.stacks 767).length + 3 + HashMassStaged.cleanupCost (temporaryCleared a)

def command (query : Cmd 40 896) : Cmd 40 896 := .seq stage (.seq query cleanup)

theorem temporary_eval (a : State 40 896) :
    Eval clearTemporary (2 * (a.stacks 767).length + 3) a (temporaryCleared a) :=
  BankRoutines.clear_call_eval (767 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks

theorem temporary_frame (a : State 40 896) (i : Fin 896) (hi : i ≠ 767) :
    (temporaryCleared a).stacks i = a.stacks i := clearStacks_frame _ _ _ hi

theorem temporary_bound (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((temporaryCleared a).stacks i).length ≤ B := by
  intro i
  by_cases hi : i = 767
  · subst i; simp [temporaryCleared]
  · simpa only [temporary_frame a i hi] using ha i

theorem stage_eval (a : State 40 896) : Eval stage (stageCost a) a (staged a) :=
  (temporary_eval a).seq (LeafOuterNative.stageFinal_eval (temporaryCleared a) (by simp [temporaryCleared]))

theorem cleanup_eval (a : State 40 896) : Eval cleanup (cleanupCost a) a (cleaned a) :=
  (temporary_eval a).seq (HashMassStaged.cleanup_eval (temporaryCleared a) (by simp [temporaryCleared]))

theorem staged_sources (a : State 40 896) :
    (staged a).stacks 700 = a.stacks 784 ∧
    (staged a).stacks 701 = a.stacks 777 ∧
    (staged a).stacks 707 = a.stacks 782 ∧
    (staged a).stacks 708 = a.stacks 783 ∧
    (staged a).stacks 709 = a.stacks 785 := by
  simpa only [staged, temporary_frame _ 784 (by decide), temporary_frame _ 777 (by decide),
    temporary_frame _ 782 (by decide), temporary_frame _ 783 (by decide),
    temporary_frame _ 785 (by decide)] using LeafOuterNative.finalStaged_sources (temporaryCleared a)

theorem staged_rows (a : State 40 896) (rows : List (List Bool))
    (hh : a.stacks 777 = HashGreedyProgram.encodedHistory rows) :
    (staged a).stacks 701 = HashGreedyProgram.encodedHistory rows :=
  (staged_sources a).2.1.trans hh

theorem staged_frame (a : State 40 896) (i : Fin 896)
    (hi : i ∉ HashMassStaged.stagedPorts) (ht : i ≠ 767) :
    (staged a).stacks i = a.stacks i := by
  have hn : i ≠ 700 ∧ i ≠ 701 ∧ i ≠ 702 ∧ i ≠ 707 ∧ i ≠ 708 ∧ i ≠ 709 := by
    simpa [HashMassStaged.stagedPorts] using hi
  exact (LeafOuterNative.finalStaged_frame _ i hn.1 hn.2.1
    hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2).trans (temporary_frame a i ht)

/-- The accepted history stage does not use the trial-prefix scratch. -/
theorem staged_702 (a : State 40 896) : (staged a).stacks 702 = a.stacks 702 :=
  (LeafOuterNative.finalStaged_frame _ 702 (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans (temporary_frame a 702 (by decide))

theorem staged_temporary (a : State 40 896) : (staged a).stacks 767 = [] := by
  change (LeafOuterNative.finalStaged (temporaryCleared a)).stacks 767 = []
  rw [LeafOuterNative.finalStaged_frame _ 767 (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  simp [temporaryCleared]

theorem staged_bound (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((staged a).stacks i).length ≤ B := by
  intro i
  have h := staged_sources a
  by_cases h0 : i = 700
  · subst i; rw [h.1]; exact ha 784
  by_cases h1 : i = 701
  · subst i; rw [h.2.1]; exact ha 777
  by_cases h7 : i = 707
  · subst i; rw [h.2.2.1]; exact ha 782
  by_cases h8 : i = 708
  · subst i; rw [h.2.2.2.1]; exact ha 783
  by_cases h9 : i = 709
  · subst i; rw [h.2.2.2.2]; exact ha 785
  change ((LeafOuterNative.finalStaged (temporaryCleared a)).stacks i).length ≤ B
  rw [LeafOuterNative.finalStaged_frame _ i h0 h1 h7 h8 h9]
  exact temporary_bound a B ha i

theorem stage_cost_le (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) : stageCost a ≤ 47 * B + 46 := by
  have h := routes_cost_bound LeafOuterNative.masterRoutes (temporaryCleared a) B
    (temporary_bound a B ha)
  have ht := ha 767
  change LeafOuterNative.stageFinalCost (temporaryCleared a) ≤ 5 * (9 * B + 8) + 3 at h
  unfold stageCost
  omega

theorem cleaned_frame (a : State 40 896) (i : Fin 896)
    (hi : i ∉ HashMassStaged.stagedPorts) (ht : i ≠ 767) :
    (cleaned a).stacks i = a.stacks i := by
  exact (BankRoutines.clearBankStacks_frame i HashMassStaged.stagedPorts
    (temporaryCleared a).stacks hi).trans (temporary_frame a i ht)

theorem cleaned_count (a : State 40 896) : (cleaned a).stacks 788 = a.stacks 788 :=
  cleaned_frame a 788 (by decide) (by decide)

theorem cleaned_empty (a : State 40 896) (i : Fin 896)
    (hi : i ∈ HashMassStaged.stagedPorts) : (cleaned a).stacks i = [] :=
  BankRoutines.clearBankStacks_mem i HashMassStaged.stagedPorts (temporaryCleared a).stacks hi

theorem cleaned_temporary (a : State 40 896) : (cleaned a).stacks 767 = [] := by
  change BankRoutines.clearBankStacks HashMassStaged.stagedPorts (temporaryCleared a).stacks 767 = []
  rw [BankRoutines.clearBankStacks_frame _ _ _ (by decide)]
  simp [temporaryCleared]

theorem cleaned_bound (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((cleaned a).stacks i).length ≤ B := by
  intro i
  by_cases hi : i ∈ HashMassStaged.stagedPorts
  · rw [cleaned_empty a i hi]; simp
  · change (BankRoutines.clearBankStacks HashMassStaged.stagedPorts
      (temporaryCleared a).stacks i).length ≤ B
    rw [BankRoutines.clearBankStacks_frame i HashMassStaged.stagedPorts
      (temporaryCleared a).stacks hi]
    exact temporary_bound a B ha i

theorem cleanup_cost_le (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) : cleanupCost a ≤ 14 * B + 24 := by
  have hc : (HashMassStaged.stagedPorts.map
      (fun i => ((temporaryCleared a).stacks i).length)).sum ≤ 6 * B := by
    have h := List.sum_le_length_nsmul
      (HashMassStaged.stagedPorts.map (fun i => ((temporaryCleared a).stacks i).length)) B
      (by intro x hx; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx; exact temporary_bound a B ha i)
    simpa [HashMassStaged.stagedPorts] using h
  have ht := ha 767
  unfold cleanupCost HashMassStaged.cleanupCost
  omega

/-- Cleanup removes only the physical staging buffers and temporary. If the
actual query restores its other inputs, the complete count is the sole change. -/
theorem restored_stacks (a b : State 40 896) (count : List Bool)
    (ht : a.stacks 767 = []) (he : ∀ i ∈ HashMassStaged.stagedPorts, a.stacks i = [])
    (hb : b.stacks = Function.update (staged a).stacks 788 count) :
    (cleaned b).stacks = Function.update a.stacks 788 count := by
  funext i
  by_cases hi : i ∈ HashMassStaged.stagedPorts
  · have hn : i ≠ 788 := by
      intro h; subst i; exact (by decide : (788 : Fin 896) ∉ HashMassStaged.stagedPorts) hi
    rw [cleaned_empty b i hi, Function.update_of_ne hn, he i hi]
  · by_cases ht' : i = 767
    · subst i
      rw [cleaned_temporary, Function.update_of_ne (by decide : (767 : Fin 896) ≠ 788), ht]
    · rw [cleaned_frame b i hi ht', hb]
      by_cases hc : i = 788
      · subst i; simp
      · rw [Function.update_of_ne hc, Function.update_of_ne hc, staged_frame a i hi ht']

private theorem sequence_prefix {first second : Cmd 40 896} {n m bound : ℕ}
    {a b c : State 40 896} (hf : Eval first n a b) (hs : Eval second m b c)
    (hfirst : ∀ p q, p ≤ n → Trace (compiled first 784 788) p
      (a.withPC (some (compiled first 784 788).entry)) q → ∀ i, (q.stacks i).length ≤ bound)
    (hsecond : ∀ p q, p ≤ m → Trace (compiled second 784 788) p
      (b.withPC (some (compiled second 784 788).entry)) q → ∀ i, (q.stacks i).length ≤ bound) :
    ∀ p q, p ≤ n + m → Trace (compiled (.seq first second) 784 788) p
      (a.withPC (some (compiled (.seq first second) 784 788).entry)) q →
      ∀ i, (q.stacks i).length ≤ bound :=
  StructuredSpace.sequence_stack_bound hf hs 784 788 hfirst hsecond
    (compiled (.seq first second) 784 788) (siteAddress _) (exitAddress _)
    (compiled_site _ 784 788)

/-- Actual evaluation and prefix proofs of the chosen query compose without
using its possibly exponential duration as a storage bound. -/
theorem run_of_eval (query : Cmd 40 896) (a b : State 40 896) (n B C : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B)
    (hb : ∀ i, (b.stacks i).length ≤ B)
    (hq : Eval query n (staged a) b)
    (hspace : ∀ p z, p ≤ n → Trace (compiled query 784 788) p
      ((staged a).withPC (some (compiled query 784 788).entry)) z →
      ∀ i, (z.stacks i).length ≤ C) :
    let steps := stageCost a + (n + cleanupCost b)
    Eval (command query) steps a (cleaned b) ∧
      steps + 1 ≤ n + 61 * B + 71 ∧
      Trace (compiled (command query) 784 788) (steps + 1)
        (a.withPC (some (compiled (command query) 784 788).entry)) ((cleaned b).withPC none) ∧
      (cleaned b).stacks 788 = b.stacks 788 ∧
      (∀ i, ((cleaned b).stacks i).length ≤ B) ∧
      ∀ p z, p ≤ steps + 1 → Trace (compiled (command query) 784 788) p
        (a.withPC (some (compiled (command query) 784 788).entry)) z →
        ∀ i, (z.stacks i).length ≤ max C (1000 * B + 100) := by
  dsimp only
  have hs := stage_eval a
  have hc := cleanup_eval b
  have whole := hs.seq (hq.seq hc)
  have hst := stage_cost_le a B ha
  have hct := cleanup_cost_le b B hb
  have hsbound : ∀ p z, p ≤ stageCost a → Trace (compiled stage 784 788) p
      (a.withPC (some (compiled stage 784 788).entry)) z →
      ∀ i, (z.stacks i).length ≤ max C (1000 * B + 100) := by
    intro p z hp hz i
    have h := StructuredSpace.local_stack_bound (compiled stage 784 788)
      (steps := 47 * B + 46) (StreamResources.dataBits_le_mul _ ha) p z (hp.trans hst) hz i
    exact h.trans (le_max_of_le_right (by omega))
  have hcbound : ∀ p z, p ≤ cleanupCost b → Trace (compiled cleanup 784 788) p
      (b.withPC (some (compiled cleanup 784 788).entry)) z →
      ∀ i, (z.stacks i).length ≤ max C (1000 * B + 100) := by
    intro p z hp hz i
    have h := StructuredSpace.local_stack_bound (compiled cleanup 784 788)
      (steps := 14 * B + 24) (StreamResources.dataBits_le_mul _ hb) p z (hp.trans hct) hz i
    exact h.trans (le_max_of_le_right (by omega))
  have hqbound : ∀ p z, p ≤ n → Trace (compiled query 784 788) p
      ((staged a).withPC (some (compiled query 784 788).entry)) z →
      ∀ i, (z.stacks i).length ≤ max C (1000 * B + 100) := by
    intro p z hp hz i
    exact (hspace p z hp hz i).trans (le_max_left _ _)
  refine ⟨whole, by omega, compiled_halt_trace whole 784 788,
    cleaned_count b, cleaned_bound b B hb, ?_⟩
  exact StructuredSpace.compiled_halt_stack_bound whole 784 788
    (sequence_prefix hs (hq.seq hc) hsbound (sequence_prefix hq hc hqbound hcbound))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage
