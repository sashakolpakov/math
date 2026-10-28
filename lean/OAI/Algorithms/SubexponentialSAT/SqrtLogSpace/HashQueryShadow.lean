import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryInputBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackTransport
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds

/-! The literal staged collector entry has a uniformly bounded proof shadow.
Only the five caller words left unrestricted by the query-time binder are
erased. No executable instruction, query evaluation, or semantic answer is
assumed in these physical input bounds. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow

open BitProgram StructuredCalls SqrtLog ProgramTapeReplay
open HashMassAdapter HashGreedyExecution

local notation "H" => (fun i : Fin 896 => Fin.val i = 320 ∨ Fin.val i = 322 ∨
  Fin.val i = 770 ∨ Fin.val i = 771 ∨ Fin.val i = 781)

private theorem encoded_singleton_length (word : List Bool) :
    (Encoding.encodeList id [word]).length = 2 * word.length + 3 := by
  simp [Encoding.encodeList]

/-- A candidate boundary has only three visible changing words: history,
framed counter, and the empty scratch. The incumbent and outer unary counter
remain completely unrestricted. -/
theorem boundary_visible_bound (base d : State 40 896) (L : ℕ)
    (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i)
    (hhistory : (d.stacks 777).length ≤ L)
    (hcounter : (d.stacks 778).length ≤ L) (hscratch : d.stacks 779 = []) :
    ∀ i, ¬ H i → (d.stacks i).length ≤ L := by
  intro i hi
  by_cases h777 : i = 777
  · subst i; exact hhistory
  by_cases h778 : i = 778
  · subst i; exact hcounter
  by_cases h779 : i = 779
  · subst i; simp [hscratch]
  have hne (j : Fin 896) (hj : H j) : i ≠ j := by
    intro he
    subst i
    exact hi hj
  rw [hframe i (hne 770 (by decide)) (hne 771 (by decide)) h777 h778 h779
    (hne 781 (by decide))]
  exact hbase i

/-- Normalization has the declared fixed payload width even for losing or
padded counter words. All other visible words retain their actual contents. -/
theorem trial_visible_bound (d : State 40 896) (m depth L : ℕ) (word : List Bool)
    (hd : ∀ i, ¬ H i → (d.stacks i).length ≤ L)
    (hC : HashCandidates.payloadWidth m depth ≤ L) :
    ∀ i, ¬ H i → ((trialState d m depth word).stacks i).length ≤ L := by
  intro i hi
  by_cases h768 : i = 768
  · subst i
    simpa [trialState] using hC
  · simpa only [trialState, Function.update_of_ne h768] using hd i hi

/-- Actual trial staging copies only visible sources and prefixes the actual
candidate to the actual history. It does not copy any erased caller word. -/
theorem staged_visible_bound (a : State 40 896) (L : ℕ)
    (ha : ∀ i, ¬ H i → (a.stacks i).length ≤ L) :
    ∀ i, ¬ H i → ((LeafOuterNative.trialStaged a).stacks i).length ≤ 3 * L + 2 := by
  intro i hi
  have hsrc := LeafOuterNative.trialStaged_sources a
  by_cases hs : i ∈ HashMassStaged.stagedPorts
  · simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hsrc.1]; have := ha 784 (by decide); omega
    · rw [hsrc.2.1]
      simp only [List.length_cons, List.length_append, Encoding.length_frame, List.length_reverse]
      have := ha 768 (by decide)
      have := ha 777 (by decide)
      omega
    · rw [show (LeafOuterNative.trialStaged a).stacks 702 = [] from
        LeafOuterNative.prefixed_scratch _]
      simp
    · rw [hsrc.2.2.1]; have := ha 782 (by decide); omega
    · rw [hsrc.2.2.2.1]; have := ha 783 (by decide); omega
    · rw [hsrc.2.2.2.2]; have := ha 785 (by decide); omega
  · rw [HashMassStaged.staged_frame a i hs]
    have := ha i hi
    omega

/-- At the real parser callback,321 is the current finite reference and
323/324 are empty. The unread tail320 and accumulated mass322 may have any
length; they disappear only in this proof-side shadow. -/
theorem record_shadow_bound (staged a : State 40 896) (L : ℕ)
    (hstage : ∀ i, ¬ H i → (staged.stacks i).length ≤ L)
    (hready : Ready (fun ws => ws = workspace staged) a)
    (tail bits : List Bool) (hbits : bits.length ≤ L) :
    ∀ i, ((rebaseState H (fun _ => [])
      (RecordPrograms.state recordPorts a false true false tail bits.reverse)).stacks i).length ≤ L := by
  apply CommandStackTransport.shadow_stack_bound
  intro i hi
  by_cases h321 : i = 321
  · subst i
    simpa [RecordPrograms.state, recordPorts] using hbits
  by_cases h323 : i = 323
  · subst i
    simp [RecordPrograms.state, recordPorts, hready.result_empty]
  by_cases h324 : i = 324
  · subst i
    simp [RecordPrograms.state, recordPorts, hready.scratch_empty]
  have h320 : i ≠ 320 := by
    intro he; subst i; exact hi (by decide)
  have h322 : i ≠ 322 := by
    intro he; subst i; exact hi (by decide)
  have hf := workspace_frame staged a hready.workspace_ready i h320 h321 h322 h323 h324
  simpa only [RecordPrograms.state, recordPorts, Function.update_of_ne h320,
    Function.update_of_ne h321, hf] using hstage i hi

/-- This is the exact physical marked entry quantified by staged_rounds_eval.
All length assumptions concern the fixed prepared base and the explicitly
bounded history/candidate domain, never the five suspended caller words. -/
theorem marked_shadow_bound (base d a : State 40 896) (m depth L : ℕ)
    (word tail : List Bool) (e : Fin m)
    (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i)
    (hhistory : (d.stacks 777).length ≤ L)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hcounter : d.stacks 778 = Encoding.encodeList id [word])
    (hscratch : d.stacks 779 = [])
    (hcounterBound : 2 * HashCandidates.payloadWidth m depth + 3 ≤ L) (hm : m ≤ L)
    (hready : Ready (fun ws => ws = workspace
      (LeafOuterNative.trialStaged (trialState d m depth word))) a) :
    ∀ i, ((rebaseState H (fun _ => [])
      (RecordPrograms.state recordPorts a false true false tail
        (Encoding.encodeNat e.val).reverse)).stacks i).length ≤ 3 * L + 2 := by
  have hc : (d.stacks 778).length ≤ L := by
    rw [hcounter, encoded_singleton_length, hword]
    omega
  have hd := boundary_visible_bound base d L hbase hframe hhistory hc hscratch
  have ht := trial_visible_bound d m depth L word hd (by omega)
  apply record_shadow_bound _ a (3 * L + 2) (staged_visible_bound _ L ht) hready
  simp only [Encoding.length_encodeNat]
  have he := e.isLt
  omega

/-- The exact staged-round caller already bounds the complete encoded
reference stream. Its actual current reference is a member of that stream,
so no additional clause-count inequality is required. -/
theorem marked_shadow_bound_of_references (base d a : State 40 896) (m depth L : ℕ)
    (word tail : List Bool) (e : Fin m)
    (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i)
    (hhistory : (d.stacks 777).length ≤ L)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hcounter : d.stacks 778 = Encoding.encodeList id [word])
    (hscratch : d.stacks 779 = [])
    (hcounterBound : 2 * HashCandidates.payloadWidth m depth + 3 ≤ L)
    (href : (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2)
    (hready : Ready (fun ws => ws = workspace
      (LeafOuterNative.trialStaged (trialState d m depth word))) a) :
    ∀ i, ((rebaseState H (fun _ => [])
      (RecordPrograms.state recordPorts a false true false tail
        (Encoding.encodeNat e.val).reverse)).stacks i).length ≤ 3 * L + 2 := by
  have hc : (d.stacks 778).length ≤ L := by
    rw [hcounter, encoded_singleton_length, hword]
    omega
  have hd := boundary_visible_bound base d L hbase hframe hhistory hc hscratch
  have ht := trial_visible_bound d m depth L word hd (by omega)
  apply record_shadow_bound _ a (3 * L + 2) (staged_visible_bound _ L ht) hready
  exact (LeafScopeInputBounds.encoded_member_length id _ _
    ((RowSelectionProgram.Index.mem_alphabet m e.val).mpr e.isLt)).trans href

/-- History-only staging copies visible master words and physically clears
its temporary. It needs no bound on remaining caller counters. -/
theorem accepted_staged_visible_bound (a : State 40 896) (L : ℕ)
    (ha : ∀ i, ¬ H i → (a.stacks i).length ≤ L) :
    ∀ i, ¬ H i → ((AcceptedQueryStage.staged a).stacks i).length ≤ L := by
  intro i hi
  have h := AcceptedQueryStage.staged_sources a
  by_cases h0 : i = 700
  · subst i; rw [h.1]; exact ha 784 (by decide)
  by_cases h1 : i = 701
  · subst i; rw [h.2.1]; exact ha 777 (by decide)
  by_cases h7 : i = 707
  · subst i; rw [h.2.2.1]; exact ha 782 (by decide)
  by_cases h8 : i = 708
  · subst i; rw [h.2.2.2.1]; exact ha 783 (by decide)
  by_cases h9 : i = 709
  · subst i; rw [h.2.2.2.2]; exact ha 785 (by decide)
  by_cases h702 : i = 702
  · subst i; rw [AcceptedQueryStage.staged_702]; exact ha 702 (by decide)
  by_cases h767 : i = 767
  · subst i; rw [AcceptedQueryStage.staged_temporary]; simp
  rw [AcceptedQueryStage.staged_frame a i (by
    simpa [HashMassStaged.stagedPorts] using
      (show i ≠ 700 ∧ i ≠ 701 ∧ i ≠ 702 ∧ i ≠ 707 ∧ i ≠ 708 ∧ i ≠ 709 from
        ⟨h0,h1,h702,h7,h8,h9⟩)) h767]
  exact ha i hi

/-- The actual final RowBoundary suffices for the accepted entry shadow.
Its remaining-round word781 is unrestricted and erased, while the physical
history byte cap is retained. -/
theorem accepted_shadow_bound (base selected : State 40 896) (rows : List (List Bool)) (L : ℕ)
    (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hboundary : HashGreedyRound.RowBoundary base rows selected)
    (hhistory : (HashGreedyProgram.encodedHistory rows).length ≤ L) :
    ∀ i, ((rebaseState H (fun _ => []) (AcceptedQueryStage.staged selected)).stacks i).length ≤ L := by
  apply CommandStackTransport.shadow_stack_bound
  apply accepted_staged_visible_bound
  intro i hi
  by_cases h777 : i = 777
  · subst i
    simpa only [hboundary.history] using hhistory
  have h781 : i ≠ 781 := by
    intro he; subst i; exact hi (by decide)
  rw [hboundary.frame i h777 h781]
  exact hbase i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow
