import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn

/-! Concrete outer count execution. The final canonicalization and marked
return consume the entire accumulated binary count. Their compact boundary is
proved separately from the transient workspace used by the query. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution

open OAI BitProgram StructuredCalls HighQueryAdapter DisjointReuse
open HashGreedyProgram.NativeRound

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

/-- The actual unsigned normalizer is run once after all high assignments. -/
def canonicalize : Code := .call CanonicalHigh.program
noncomputable def canonicalized (a : Data) : Data :=
  CanonicalHigh.result (CanonicalHigh.resetState a)

@[simp] theorem canonicalized_count (a : Data) :
    (canonicalized a).stacks 788 = countWord (BinaryArithmetic.toNat (a.stacks 788)) :=
  CanonicalHigh.final_count a

@[simp] theorem canonicalized_scratch (a : Data) :
    (canonicalized a).stacks 793 = [] ∧ (canonicalized a).stacks 794 = [] := by
  constructor
  · exact embedState_stack CanonicalHigh.regMap CanonicalHigh.stackMap
      (CanonicalHigh.resetState a) _ (by decide) 1
  · exact embedState_stack CanonicalHigh.regMap CanonicalHigh.stackMap
      (CanonicalHigh.resetState a) _ (by decide) 2

theorem canonicalized_frame (a : Data) (i : Fin 896)
    (h788 : i ≠ 788) (h793 : i ≠ 793) (h794 : i ≠ 794) :
    (canonicalized a).stacks i = a.stacks i := CanonicalHigh.final_frame a i h788 h793 h794

/-- No transient query cap is fed back into the retained-word bound. -/
theorem canonicalized_bound (a : Data) (n B : ℕ)
    (hcount : BinaryArithmetic.toNat (a.stacks 788) ≤ 2 ^ n) (hn : n + 1 ≤ B)
    (hframe : ∀ i, i ≠ 788 → i ≠ 793 → i ≠ 794 → (a.stacks i).length ≤ B) :
    ∀ i, ((canonicalized a).stacks i).length ≤ B := by
  intro i
  by_cases hc : i = 788
  · subst i
    exact (CanonicalHigh.final_width a n hcount).trans hn
  · by_cases hs : i = 793
    · subst i
      rw [(canonicalized_scratch a).1]
      exact Nat.zero_le _
    · by_cases ht : i = 794
      · subst i
        rw [(canonicalized_scratch a).2]
        exact Nat.zero_le _
      · rw [canonicalized_frame a i hc hs ht]
        exact hframe i hc hs ht

/-- The whole-count readback does not use the count head as a SAT bit. -/
def markedReturn : Code := .seq canonicalize HashMarkedReturn.command
noncomputable def returned (a : Data) : Data := HashMarkedReturn.result (canonicalized a)

@[simp] theorem returned_count (a : Data) :
    (returned a).stacks 323 = countWord (BinaryArithmetic.toNat (a.stacks 788)) := by
  rw [returned,HashMarkedReturn.result_count,canonicalized_count]

theorem returned_parser (a : Data) :
    (returned a).regs 16 = false ∧ (returned a).regs 17 = true ∧
      (returned a).regs 18 = false := HashMarkedReturn.result_parser _

/-- Cleanup preserves exactly the caller words in the fixed marked-query ABI.
The high accumulator is first normalized and copied in full, then reclaimed. -/
theorem returned_stacks (a : Data) (i : Fin 896) :
    (returned a).stacks i =
      if i = 323 then countWord (BinaryArithmetic.toNat (a.stacks 788))
      else if HashMarkedReturn.kept i then a.stacks i else [] := by
  rw [returned,HashMarkedReturn.result_stacks,canonicalized_count]
  split_ifs with hc hk
  · rfl
  · have hi : i ≠ 788 ∧ i ≠ 793 ∧ i ≠ 794 := by
      simp only [HashMarkedReturn.kept,decide_eq_true_eq,Fin.ext_iff] at hk ⊢
      omega
    exact canonicalized_frame a i hi.1 hi.2.1 hi.2.2
  · rfl

theorem returned_bound (a : Data) (n B : ℕ)
    (hcount : BinaryArithmetic.toNat (a.stacks 788) ≤ 2 ^ n) (hn : n + 1 ≤ B)
    (hkept : ∀ i, HashMarkedReturn.kept i = true → (a.stacks i).length ≤ B) :
    ∀ i, ((returned a).stacks i).length ≤ B := by
  intro i
  rw [returned_stacks]
  split_ifs with hc hk
  · exact (countWord_length_le hcount).trans hn
  · exact hkept i hk
  · exact Nat.zero_le _

/-- Actual canonicalization and cleanup on the same run, with an independent
all-prefix cap. This local suffix has no evaluator or successful-layout input. -/
theorem markedReturn_trace_space (a : Data) (n D : ℕ)
    (hcount : BinaryArithmetic.toNat (a.stacks 788) ≤ 2 ^ n) (hn : n + 1 ≤ D)
    (hD : ∀ i, (a.stacks i).length ≤ D) (ht : a.stacks 767 = []) :
    ∃ steps, Eval markedReturn steps a (returned a) ∧
      steps + 1 ≤ 3421 * D + 5136 ∧
      Trace (compiled markedReturn 778 777) (steps + 1)
        (a.withPC (some (compiled markedReturn 778 777).entry)) ((returned a).withPC none) ∧
      StageSpace markedReturn (steps + 1) a (931 * D + 54) := by
  obtain ⟨nc,hcanonical,hnc,hcanonicalSpace⟩ := CanonicalHigh.trace_space a D hD
  have hec : Eval canonicalize nc a (canonicalized a) := Eval.call _ hcanonical
  have hcb : ∀ i, ((canonicalized a).stacks i).length ≤ D :=
    canonicalized_bound a n D hcount hn (fun i _ _ _ => hD i)
  have hct : (canonicalized a).stacks 767 = [] :=
    (canonicalized_frame a 767 (by decide) (by decide) (by decide)).trans ht
  have her := HashMarkedReturn.eval (canonicalized a) hct
  obtain ⟨_,hrcost,hrspace⟩ := HashMarkedReturn.trace_space (canonicalized a) D hcb hct
  have he : Eval markedReturn (nc + HashMarkedReturn.cost (canonicalized a)) a (returned a) :=
    hec.seq her
  have hcspace : StageSpace canonicalize nc a (931 * D + 54) := by
    constructor
    apply StructuredSpace.call_stack_bound _ _ _ _ (compiled_site canonicalize 778 777) hcanonical
    intro k z hk hz i
    have hi := hcanonicalSpace k z hk hz i
    omega
  have hrspace' : StageSpace HashMarkedReturn.command
      (HashMarkedReturn.cost (canonicalized a)) (canonicalized a) (931 * D + 54) :=
    ⟨fun k z hk hz => hrspace.bound k z (by omega) hz⟩
  have hseq := hcspace.seq hec her hrspace'
  refine ⟨_,he,by omega,compiled_halt_trace he 778 777,?_⟩
  exact ⟨StructuredSpace.compiled_halt_stack_bound he 778 777 hseq.bound⟩

/-- The canonical marked result has the exact parser presentation consumed by
all-mark accumulation. -/
theorem returned_record (a : Data) :
    RecordPrograms.state HashMassAdapter.recordPorts (returned a) false true false
      (a.stacks 320) [] = returned a := by
  have h := HashMarkedReturn.result_record (canonicalized a)
  rwa [canonicalized_frame a 320 (by decide) (by decide) (by decide)] at h

theorem returned_workspace (entry a : Data)
    (hframe : ∀ i, HashMarkedReturn.kept i = true → a.stacks i = entry.stacks i)
    (hblank : ∀ i, HashMarkedReturn.kept i = false →
      (i.val < 320 ∨ 324 < i.val) → entry.stacks i = []) :
    HashMassAdapter.workspace (returned a) = HashMassAdapter.workspace entry := by
  apply HashMarkedReturn.workspace_restore entry (canonicalized a) _ hblank
  intro i hi
  have hn : i ≠ 788 ∧ i ≠ 793 ∧ i ≠ 794 := by
    simp only [HashMarkedReturn.kept,decide_eq_true_eq,Fin.ext_iff] at hi ⊢
    omega
  rw [canonicalized_frame a i hn.1 hn.2.1 hn.2.2]
  exact hframe i hi

open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram OAI.Algorithms.SubexponentialSAT.StackRoutines

/-- Reuse the complete cleanup, then physically put the canonical word back on
788 for the final unmarked query. The temporary marked-output word is erased. -/
def installAccepted : Code := .seq (route (323,788)) (.call (clearProgram 323 0 1))
noncomputable def installedAccepted (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,Function.update (Function.update a.stacks 788 (a.stacks 323)) 323 []⟩
def acceptedReturn : Code := .seq markedReturn installAccepted
noncomputable def accepted (a : Data) : Data := installedAccepted (returned a)

theorem installAccepted_eval (a : Data) (ht : a.stacks 767 = []) :
    Eval installAccepted
      (2 * (a.stacks 788).length + 9 * (a.stacks 323).length + 11) a (installedAccepted a) := by
  have hr := route_eval (323,788) (by unfold routeValid; decide) a ht
  have hc := BankRoutines.clear_call_eval (323 : Fin 896) (0 : Fin 40) 1
    (routed (323,788) a).regs (routed (323,788) a).stacks
  simp only [routed,Function.update_of_ne (by decide : (323 : Fin 896) ≠ 788),
    readRegs_reset] at hc
  convert hr.seq hc using 1
  · rfl
  · dsimp [routeCost]
    omega
  · rfl

/-- The accepted-query ABI returns only788. All marker, high-iterator and
query-owned scratch ports have paid cleanup instructions. -/
theorem accepted_stacks (a : Data) (i : Fin 896) :
    (accepted a).stacks i =
      if i = 788 then countWord (BinaryArithmetic.toNat (a.stacks 788))
      else if HashMarkedReturn.kept i then a.stacks i else [] := by
  simp only [accepted,installedAccepted,Function.update_apply]
  by_cases h323 : i = 323
  · subst i
    simp [HashMarkedReturn.kept,Fin.coe_ofNat_eq_mod]
  · by_cases h788 : i = 788
    · subst i
      simp [returned_count]
    · simp only [ite_eq_right h323, ite_eq_right h788, returned_stacks]

@[simp] theorem accepted_count (a : Data) :
    (accepted a).stacks 788 = countWord (BinaryArithmetic.toNat (a.stacks 788)) := by
  simp [accepted_stacks]

theorem accepted_exact_frame (entry a : Data)
    (hframe : ∀ i, HashMarkedReturn.kept i = true → a.stacks i = entry.stacks i)
    (hblank : ∀ i, i ≠ 788 → HashMarkedReturn.kept i = false → entry.stacks i = []) :
    (accepted a).stacks = Function.update entry.stacks 788
      (countWord (BinaryArithmetic.toNat (a.stacks 788))) := by
  funext i
  rw [accepted_stacks,Function.update_apply]
  split_ifs with hc hk
  · rfl
  · exact hframe i hk
  · exact (hblank i hc (Bool.eq_false_iff.mpr hk)).symm

theorem accepted_bound (a : Data) (n B : ℕ)
    (hcount : BinaryArithmetic.toNat (a.stacks 788) ≤ 2 ^ n) (hn : n + 1 ≤ B)
    (hkept : ∀ i, HashMarkedReturn.kept i = true → (a.stacks i).length ≤ B) :
    ∀ i, ((accepted a).stacks i).length ≤ B := by
  intro i
  rw [accepted_stacks]
  split_ifs with hc hk
  · exact (countWord_length_le hcount).trans hn
  · exact hkept i hk
  · exact Nat.zero_le _

private theorem installAccepted_space (a : Data) (D : ℕ)
    (hD : ∀ i, (a.stacks i).length ≤ D) :
    StageSpace installAccepted
      (2 * (a.stacks 788).length + 9 * (a.stacks 323).length + 11) a (931 * D + 54) := by
  constructor
  intro k z hk hz i
  have hin : dataBits (a.withPC (some (compiled installAccepted 778 777).entry)) ≤ 896 * D :=
    StreamResources.dataBits_le_mul _ hD
  have ht : k ≤ 11 * D + 11 := by
    have h788 := hD 788
    have h323 := hD 323
    omega
  have hi := StructuredSpace.local_stack_bound (compiled installAccepted 778 777)
    (steps := 11 * D + 11) hin k z ht hz i
  omega

/-- Final unmarked readback uses the same actual canonicalization and paid
cleanup, then a measured copy and clear. The transient cap is uniform. -/
theorem acceptedReturn_trace_space (a : Data) (n D : ℕ)
    (hcount : BinaryArithmetic.toNat (a.stacks 788) ≤ 2 ^ n) (hn : n + 1 ≤ D)
    (hD : ∀ i, (a.stacks i).length ≤ D) (ht : a.stacks 767 = []) :
    ∃ steps, Eval acceptedReturn steps a (accepted a) ∧
      steps + 1 ≤ 3430 * D + 5147 ∧
      Trace (compiled acceptedReturn 778 777) (steps + 1)
        (a.withPC (some (compiled acceptedReturn 778 777).entry)) ((accepted a).withPC none) ∧
      StageSpace acceptedReturn (steps + 1) a (931 * D + 54) := by
  obtain ⟨nm,hem,hmt,htrace,hmspace⟩ := markedReturn_trace_space a n D hcount hn hD ht
  have hrb := returned_bound a n D hcount hn (fun i _ => hD i)
  have hrt : (returned a).stacks 767 = [] := by
    simpa [returned_stacks,HashMarkedReturn.kept,Fin.coe_ofNat_eq_mod] using ht
  have hr788 : (returned a).stacks 788 = [] := by
    simp [returned_stacks,HashMarkedReturn.kept,Fin.coe_ofNat_eq_mod]
  have hei := installAccepted_eval (returned a) hrt
  have hit : 2 * ((returned a).stacks 788).length +
      9 * ((returned a).stacks 323).length + 11 ≤ 9 * D + 11 := by
    rw [hr788]
    have h323 := hrb 323
    simp only [List.length_nil,Nat.mul_zero,zero_add]
    omega
  have hispace := installAccepted_space (returned a) D hrb
  have he := hem.seq hei
  have hmspace' : StageSpace markedReturn nm a (931 * D + 54) :=
    ⟨fun k z hk hz => hmspace.bound k z (by omega) hz⟩
  have hs := StageSpace.seq hem hei hmspace' hispace
  refine ⟨_,he,by omega,compiled_halt_trace he 778 777,?_⟩
  exact ⟨StructuredSpace.compiled_halt_stack_bound he 778 777 hs.bound⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution
