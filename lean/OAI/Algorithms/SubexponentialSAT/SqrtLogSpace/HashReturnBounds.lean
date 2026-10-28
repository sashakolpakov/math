import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryInput

/-! Runtime of the actual marked-query return depends only on words that it
erases or returns. Preserved accumulator/source/caller words may be arbitrary;
source-prefix storage continues to use the separate all-word theorem. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashReturnBounds

open BitProgram StructuredCalls SqrtLog
open HashMarkedQueryAdapter HashMarkedReturn

private theorem cleanup_not_kept (i : Fin 896) (hi : i ∈ cleanupPorts) : kept i = false := by
  simp only [cleanupPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem finish_steps_le (a : Data) (D : ℕ)
    (hD : ∀ i, kept i = false → (a.stacks i).length ≤ D) : finishSteps a ≤ 35 * D + 53 := by
  have hsum : (cleanupPorts.map fun i => ((LeafOuterProgram.routed (788,323) a).stacks i).length).sum
      ≤ 13 * D := by
    have h := List.sum_le_length_nsmul
      (cleanupPorts.map fun i => ((LeafOuterProgram.routed (788,323) a).stacks i).length) D (by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        by_cases h323 : i = 323
        · subst i
          simpa [LeafOuterProgram.routed] using hD 788 (by decide)
        simpa [LeafOuterProgram.routed, h323] using hD i (cleanup_not_kept i hi))
    simpa [cleanupPorts] using h
  have hs := hD 788 (by decide)
  have hd := hD 323 (by decide)
  simp only [finishSteps, LeafOuterProgram.routeCost, cleanupPorts,
    List.length_cons, List.length_nil] at *
  omega

private theorem finish_discarded_bound (a : Data) (D : ℕ)
    (hD : ∀ i, kept i = false → (a.stacks i).length ≤ D) :
    ∀ i, kept i = false → ((finishState a).stacks i).length ≤ D := by
  intro i hi
  rw [finishState_stacks]
  by_cases hc : i ∈ cleanupPorts
  · simp [BankRoutines.clearBankStacks, hc]
  · simp only [BankRoutines.clearBankStacks, ite_eq_right hc]
    by_cases h323 : i = 323
    · subst i
      simpa using hD 788 (by decide)
    · simpa [h323] using hD i hi

private theorem lower_not_kept (i : Fin 768) (hi : ¬LeafProgram.Query.Protected i) :
    kept (HighMarkedFrontend.stackMap i) = false := by
  rw [kept, decide_eq_false_iff_not]
  simp only [LeafProgram.Query.Protected, HighMarkedFrontend.stackMap, Fin.ext_iff,
    Fin.coe_ofNat_eq_mod, Fin.castAdd, Fin.val_castLE] at hi ⊢
  norm_num only [Nat.reduceMod, Nat.reduceAdd] at hi ⊢
  omega

private theorem lower_cost_le (a : Data) (D : ℕ)
    (hD : ∀ i, kept i = false → (a.stacks i).length ≤ D) :
    LeafProgram.Query.cleanupCost (HighMarkedFrontend.project a) ≤ 1538 * D + 2310 := by
  have hlen : LeafProgram.Query.cleanupPorts.length ≤ 768 :=
    LeafProgram.Query.cleanupPorts_length_le
  have hs : (LeafProgram.Query.cleanupPorts.map
      (fun i => ((HighMarkedFrontend.project a).stacks i).length)).sum ≤
      LeafProgram.Query.cleanupPorts.length * D := by
    have h := List.sum_le_length_nsmul (LeafProgram.Query.cleanupPorts.map
      (fun i => ((HighMarkedFrontend.project a).stacks i).length)) D (by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        exact hD (HighMarkedFrontend.stackMap i)
          (lower_not_kept i ((LeafProgram.Query.mem_cleanupPorts i).mp hi).1))
    simpa only [List.length_map, smul_eq_mul] using h
  have h699 := hD 699 (by decide)
  have hprod := Nat.mul_le_mul_right (2 * D + 3) hlen
  unfold LeafProgram.Query.cleanupCost
  change 2 * (a.stacks 699).length + 6 + 3 * LeafProgram.Query.cleanupPorts.length +
    2 * (LeafProgram.Query.cleanupPorts.map
      (fun i => ((HighMarkedFrontend.project a).stacks i).length)).sum ≤ _
  nlinarith only [hs, h699, hprod]

private theorem upper_not_kept (i : Fin 896) (hi : i ∈ upperPorts) : kept i = false := by
  have hv := (mem_upperPorts i).mp hi
  rw [kept, decide_eq_false_iff_not]
  simp only [Fin.ext_iff, Fin.coe_ofNat_eq_mod]
  omega

private theorem upper_cost_le (a : Data) (D : ℕ)
    (hD : ∀ i, kept i = false → (a.stacks i).length ≤ D) :
    upperCost (HighMarkedFrontend.cleaned a) ≤ 1792 * D + 2691 := by
  have hlen : upperPorts.length ≤ 896 := upperPorts_length_le
  have hs : (upperPorts.map fun i => ((HighMarkedFrontend.cleaned a).stacks i).length).sum
      ≤ upperPorts.length * D := by
    have h := List.sum_le_length_nsmul
      (upperPorts.map fun i => ((HighMarkedFrontend.cleaned a).stacks i).length) D (by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        have hv := (mem_upperPorts i).mp hi
        rw [HighMarkedFrontend.cleaned_upper a i (by omega)]
        exact hD i (upper_not_kept i hi))
    simpa only [List.length_map, smul_eq_mul] using h
  have hprod := Nat.mul_le_mul_right D hlen
  unfold upperCost
  omega

/-- The same actual return cost bound holds with no cap on any preserved
word, including the arbitrary retained mass accumulator322. -/
theorem cost_le_discarded (a : Data) (D : ℕ)
    (hD : ∀ i, kept i = false → (a.stacks i).length ≤ D) :
    cost a + 1 ≤ 3400 * D + 5100 := by
  have hf := finish_steps_le a D hD
  have hb := finish_discarded_bound a D hD
  have hl := lower_cost_le (finishState a) D hb
  have hu := upper_cost_le (finishState a) D hb
  unfold cost
  omega

/-- The actual collector parser preserves every workspace word. Thus the
return adapter's exact discarded-bank precondition is inherited from the
staged boundary, including query-owned upper banks. No bound or emptiness is
imposed on the unread tail320 or retained accumulator322. -/
theorem record_entry_blank (staged a : Data)
    (hready : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace staged) a)
    (hblank : ∀ i, kept i = false → (i.val < 320 ∨ 324 < i.val) → staged.stacks i = [])
    (tail bits : List Bool) :
    ∀ i, kept i = false → (i.val < 320 ∨ 324 < i.val) →
      (RecordPrograms.state HashMassAdapter.recordPorts a false true false tail bits.reverse).stacks i = [] := by
  intro i hk hi
  have hneq (j : Fin 896) (hj : 320 ≤ j.val ∧ j.val ≤ 324) : i ≠ j := by
    intro h; subst i; omega
  have hw := HashMassAdapter.workspace_recordState a false true false tail bits.reverse
  exact (HashMassAdapter.workspace_frame staged _ (hw.trans hready.workspace_ready) i
    (hneq 320 (by decide)) (hneq 321 (by decide)) (hneq 322 (by decide))
    (hneq 323 (by decide)) (hneq 324 (by decide))).trans (hblank i hk hi)

/-- The fixed cleanup/copy temporary is transported by the same actual
workspace relation even though it is a preserved caller port. -/
theorem record_entry_scratch (staged a : Data)
    (hready : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace staged) a)
    (ht : staged.stacks 767 = []) (tail bits : List Bool) :
    (RecordPrograms.state HashMassAdapter.recordPorts a false true false tail bits.reverse).stacks 767 = [] := by
  have hw := HashMassAdapter.workspace_recordState a false true false tail bits.reverse
  exact (HashMassAdapter.workspace_frame staged _ (hw.trans hready.workspace_ready) 767
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht

/-- The real lower clean-work predicate and preparation's explicit upper
query-bank frame jointly give every discarded workspace blank. -/
theorem discarded_blank_of_workspace (a : Data)
    (hlow : LeafProgram.Query.CleanWork (HighMarkedFrontend.project a))
    (hupper : ∀ i : Fin 896,
      (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) → a.stacks i = []) :
    ∀ i, kept i = false → (i.val < 320 ∨ 324 < i.val) → a.stacks i = [] := by
  intro i hk hi
  by_cases hsmall : i.val < 768
  · let j : Fin 768 := ⟨i.val, hsmall⟩
    have hp : ¬LeafProgram.Query.Protected j := by
      simp only [kept, decide_eq_false_iff_not, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hk
      simp only [LeafProgram.Query.Protected, Fin.ext_iff, Fin.coe_ofNat_eq_mod]
      dsimp only [j]
      omega
    have hj : j ≠ 321 := by
      intro he
      have hv := congrArg Fin.val he
      dsimp [j] at hv
      omega
    have h := hlow j hp hj
    change a.stacks (HighMarkedFrontend.stackMap j) = [] at h
    have he : HighMarkedFrontend.stackMap j = i := Fin.ext rfl
    rwa [he] at h
  · apply hupper i
    simp only [kept, decide_eq_false_iff_not, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hk
    have hib := i.isLt
    omega

/-- Trial staging only writes preserved immutable sources and clears702.
It therefore preserves the exact return adapter's discarded-bank condition. -/
theorem staged_discarded_blank (a : Data)
    (hblank : ∀ i, kept i = false → (i.val < 320 ∨ 324 < i.val) → a.stacks i = []) :
    ∀ i, kept i = false → (i.val < 320 ∨ 324 < i.val) →
      (LeafOuterNative.trialStaged a).stacks i = [] := by
  intro i hk hi
  by_cases h702 : i = 702
  · subst i
    exact LeafOuterNative.prefixed_scratch _
  have hout : i ∉ HashMassStaged.stagedPorts := by
    simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil,
      or_false, not_or]
    simp only [kept, decide_eq_false_iff_not, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hk
    simp only [Fin.ext_iff, Fin.coe_ofNat_eq_mod] at h702 ⊢
    omega
  rw [HashMassStaged.staged_frame a i hout]
  exact hblank i hk hi

/-- Concrete low/upper preparation facts pass through actual trial staging,
the all-mark collector workspace and its parser to the exact callback entry.
The retained accumulator and unread reference tail are unrestricted. -/
theorem staged_record_entry_blank (d a : Data)
    (hlow : LeafProgram.Query.CleanWork (HighMarkedFrontend.project d))
    (hupper : ∀ i : Fin 896,
      (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) → d.stacks i = [])
    (hready : HashMassAdapter.Ready
      (fun ws => ws = HashMassAdapter.workspace (LeafOuterNative.trialStaged d)) a)
    (tail bits : List Bool) :
    ∀ i, kept i = false → (i.val < 320 ∨ 324 < i.val) →
      (RecordPrograms.state HashMassAdapter.recordPorts a false true false tail bits.reverse).stacks i = [] :=
  record_entry_blank _ a hready
    (staged_discarded_blank d (discarded_blank_of_workspace d hlow hupper)) tail bits

theorem staged_record_entry_scratch (d a : Data)
    (hready : HashMassAdapter.Ready
      (fun ws => ws = HashMassAdapter.workspace (LeafOuterNative.trialStaged d)) a)
    (ht : d.stacks 767 = []) (tail bits : List Bool) :
    (RecordPrograms.state HashMassAdapter.recordPorts a false true false tail bits.reverse).stacks 767 = [] := by
  apply record_entry_scratch _ a hready _ tail bits
  rw [HashMassStaged.staged_frame d 767 (by decide)]
  exact ht

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashReturnBounds
