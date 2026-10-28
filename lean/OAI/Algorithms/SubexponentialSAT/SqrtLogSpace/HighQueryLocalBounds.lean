import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashReturnBounds

/-! Source-only local costs for the physical high-count controller. Retained
caller words, including the outer marked accumulator322, do not enter them. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLocalBounds
open OAI BitProgram StructuredCalls StackRoutines HighQueryAdapter

abbrev Data := State 40 896

def seedSources : List (Fin 896) := [323,330,338,788,789,790,791,792]

private theorem seed_cost_le (a : Data) (L : ℕ)
    (h : ∀ i ∈ seedSources, (a.stacks i).length ≤ L) :
    HighCountSeed.cost a + 1 ≤ 26 * L + 26 := by
  have hs : (HighCountSeed.changed.map
      (fun i => ((clearStacks 791 a.stacks) i).length)).sum ≤ 3 * L := by
    have hb : ∀ i ∈ HighCountSeed.changed,
        ((clearStacks 791 a.stacks) i).length ≤ L := by
      intro i hi
      by_cases he : i = 791
      · subst i
        simp [clearStacks]
      · simp only [HighCountSeed.changed, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · simpa [clearStacks] using h 330 (by decide)
        · exact False.elim (he rfl)
        · simpa [clearStacks] using h 792 (by decide)
    have hp := List.sum_le_length_nsmul
      (HighCountSeed.changed.map (fun i => ((clearStacks 791 a.stacks) i).length)) L
      (by intro x hx; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx; exact hb i hi)
    simpa [HighCountSeed.changed] using hp
  have h791 := h 791 (by decide)
  have hm := h 338 (by decide)
  have hc : SqrtLog.HighIncidenceProgram.Branches.trueCount (a.stacks 338) ≤
      (a.stacks 338).length := List.length_filter_le _ _
  unfold HighCountSeed.cost HighCountSeed.resetCost
  omega

private theorem init_cost_le (a : Data) (L : ℕ)
    (h330 : (a.stacks 330).length ≤ L)
    (h : ∀ i ∈ HighCountInit.changed, (a.stacks i).length ≤ L) :
    HighCountInit.cost a + 1 ≤ 21 * L + 31 := by
  have hs : (HighCountInit.changed.map
      (fun i => ((clearStacks 792 a.stacks) i).length)).sum ≤ 6 * L := by
    have hp := List.sum_le_length_nsmul
      (HighCountInit.changed.map (fun i => ((clearStacks 792 a.stacks) i).length)) L
      (by
        intro x hx
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
        by_cases he : i = 792
        · subst i; simp [clearStacks]
        · simpa [clearStacks,he] using h i hi)
    simpa [HighCountInit.changed] using hp
  have h792 := h 792 (by decide)
  unfold HighCountInit.cost HighCountInit.resetCost
  omega

/-- This is the actual current-mask initialization, with no supplied zero
counter and no bound on unrelated retained stacks. -/
theorem seed_eval (a : Data) (L : ℕ)
    (h : ∀ i ∈ seedSources, (a.stacks i).length ≤ L) :
    ∃ steps rf, steps ≤ 110 * L + 80 ∧
      Eval (.call HighCountSeed.initializeProgram) steps a (HighCountSeed.initialized a rf) := by
  obtain ⟨rf,he⟩ := HighCountSeed.command_eval a
  have hs := Eval.call HighCountSeed.program (compiled_halt_trace he 338 330)
  have hi := Eval.call HighCountInit.program
    (compiled_halt_trace (HighCountInit.command_eval (HighCountSeed.result a rf)) 330 788)
  have hcmd : Eval HighCountSeed.initializeCmd
      ((HighCountSeed.cost a + 1) + (HighCountInit.cost (HighCountSeed.result a rf) + 1))
      a (HighCountSeed.initialized a rf) := hs.seq hi
  have h330 : ((HighCountSeed.result a rf).stacks 330).length ≤ 4 * L + 1 := by
    rw [HighCountSeed.result_counter,ExecCNFTupleOdometer.encoded_length]
    simp only [List.flatten_replicate_singleton,List.length_replicate]
    have hm := h 338 (by decide)
    have hc : SqrtLog.HighIncidenceProgram.Branches.trueCount (a.stacks 338) ≤
        (a.stacks 338).length := List.length_filter_le _ _
    omega
  have hb : ∀ i ∈ HighCountInit.changed,
      ((HighCountSeed.result a rf).stacks i).length ≤ 4 * L + 1 := by
    intro i hi
    simp only [HighCountInit.changed, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [HighCountSeed.result_frame a rf 788 (by decide)]
      have := h 788 (by decide); omega
    · rw [HighCountSeed.result_frame a rf 789 (by decide)]
      have := h 789 (by decide); omega
    · rw [HighCountSeed.result_frame a rf 790 (by decide)]
      have := h 790 (by decide); omega
    · rw [HighCountSeed.result_frame a rf 323 (by decide)]
      have := h 323 (by decide); omega
    · rw [HighCountSeed.result_scratch]; simp
    · rw [HighCountSeed.result_maskcopy]; simp
  have ht1 := seed_cost_le a L h
  have ht2 := init_cost_le (HighCountSeed.result a rf) (4 * L + 1) h330 hb
  exact ⟨_,rf,by omega,Eval.call _ (compiled_halt_trace hcmd 338 789)⟩

/-- The durable high-counter refresh pays only for its source and destination
words; arbitrarily large retained collector words are irrelevant to time. -/
theorem copy_cost_le (a : Data) (L : ℕ)
    (h330 : (a.stacks 330).length ≤ L) (h792 : (a.stacks 792).length ≤ L)
    (h789 : (a.stacks 789).length ≤ L) : copyHighCost a ≤ 11 * L + 11 := by
  unfold copyHighCost
  omega

/-- Canonical unsigned readback runs on the actual accumulator and its two
scratch words. This is a source-only time statement, separate from prefix space. -/
theorem canonicalize_eval (a : Data) (L : ℕ)
    (h788 : (a.stacks 788).length ≤ L) (h793 : (a.stacks 793).length ≤ L)
    (h794 : (a.stacks 794).length ≤ L) :
    ∃ steps, steps ≤ 21 * L + 36 ∧
      Eval HighQueryExecution.canonicalize steps a (HighQueryExecution.canonicalized a) := by
  obtain ⟨steps,ht,he⟩ := CanonicalHigh.command_eval (CanonicalHigh.resetState a)
    (by simp [CanonicalHigh.resetState,clearStacks])
    (by simp [CanonicalHigh.resetState,clearStacks])
  have h788' : (CanonicalHigh.resetState a).stacks 788 = a.stacks 788 := by
    simp [CanonicalHigh.resetState,clearStacks]
  rw [h788'] at ht
  have hr := (CanonicalHigh.reset_eval a).seq he
  exact ⟨_,by omega,Eval.call _ (compiled_halt_trace hr 788 788)⟩

/-- Canonicalization preserves the active source cap while leaving arbitrary
retained caller words outside the time argument. -/
private theorem canonicalized_discarded (a : Data) (n L : ℕ)
    (hcount : BinaryArithmetic.toNat (a.stacks 788) ≤ 2 ^ n) (hn : n + 1 ≤ L)
    (h : ∀ i, HashMarkedReturn.kept i = false → (a.stacks i).length ≤ L) :
    ∀ i, HashMarkedReturn.kept i = false →
      ((HighQueryExecution.canonicalized a).stacks i).length ≤ L := by
  intro i hi
  by_cases h788 : i = 788
  · subst i
    exact (CanonicalHigh.final_width a n hcount).trans hn
  · by_cases h793 : i = 793
    · subst i
      rw [(HighQueryExecution.canonicalized_scratch a).1]
      exact Nat.zero_le _
    · by_cases h794 : i = 794
      · subst i
        rw [(HighQueryExecution.canonicalized_scratch a).2]
        exact Nat.zero_le _
      · rw [HighQueryExecution.canonicalized_frame a i h788 h793 h794]
        exact h i hi

/-- Complete marked readback and cleanup has source-only time on the actual
run. In particular neither the clause tail320 nor accumulator322 is scanned. -/
theorem markedReturn_eval (a : Data) (n L : ℕ)
    (hcount : BinaryArithmetic.toNat (a.stacks 788) ≤ 2 ^ n) (hn : n + 1 ≤ L)
    (h : ∀ i, HashMarkedReturn.kept i = false → (a.stacks i).length ≤ L)
    (ht : a.stacks 767 = []) :
    ∃ steps, steps + 1 ≤ 3421 * L + 5136 ∧
      Eval HighQueryExecution.markedReturn steps a (HighQueryExecution.returned a) := by
  obtain ⟨nc,hnc,hec⟩ := canonicalize_eval a L
    (h 788 (by decide)) (h 793 (by decide)) (h 794 (by decide))
  have hc := canonicalized_discarded a n L hcount hn h
  have hct : (HighQueryExecution.canonicalized a).stacks 767 = [] :=
    (HighQueryExecution.canonicalized_frame a 767 (by decide) (by decide) (by decide)).trans ht
  have he := HashMarkedReturn.eval (HighQueryExecution.canonicalized a) hct
  have hcost := HashReturnBounds.cost_le_discarded (HighQueryExecution.canonicalized a) L hc
  exact ⟨_,by omega,hec.seq he⟩

/-- The final accepted query uses the same cleanup and a real copy back788.
The single canonical count word is the only extra word read by this suffix. -/
theorem acceptedReturn_eval (a : Data) (n L : ℕ)
    (hcount : BinaryArithmetic.toNat (a.stacks 788) ≤ 2 ^ n) (hn : n + 1 ≤ L)
    (h : ∀ i, HashMarkedReturn.kept i = false → (a.stacks i).length ≤ L)
    (ht : a.stacks 767 = []) :
    ∃ steps, steps + 1 ≤ 3430 * L + 5147 ∧
      Eval HighQueryExecution.acceptedReturn steps a (HighQueryExecution.accepted a) := by
  obtain ⟨nm,hnm,hem⟩ := markedReturn_eval a n L hcount hn h ht
  have hrt : (HighQueryExecution.returned a).stacks 767 = [] := by
    simpa [HighQueryExecution.returned_stacks,HashMarkedReturn.kept,Fin.coe_ofNat_eq_mod] using ht
  have h788 : (HighQueryExecution.returned a).stacks 788 = [] := by
    simp [HighQueryExecution.returned_stacks,HashMarkedReturn.kept,Fin.coe_ofNat_eq_mod]
  have h323 : ((HighQueryExecution.returned a).stacks 323).length ≤ L := by
    rw [HighQueryExecution.returned_count]
    exact (countWord_length_le hcount).trans hn
  have hei := HighQueryExecution.installAccepted_eval (HighQueryExecution.returned a) hrt
  have hcost : 2 * ((HighQueryExecution.returned a).stacks 788).length +
      9 * ((HighQueryExecution.returned a).stacks 323).length + 11 ≤ 9 * L + 11 := by
    rw [h788]
    simp only [List.length_nil,Nat.mul_zero,zero_add]
    omega
  exact ⟨_,by omega,hem.seq hei⟩

open HashGreedyProgram.NativeRound

/-- Source-only seed time and all-prefix caller space are properties of the
same fixed actual run, identified by deterministic execution. -/
theorem seed_resources (a : Data) (L D : ℕ)
    (hL : ∀ i ∈ seedSources, (a.stacks i).length ≤ L)
    (hlocal : 12 * L + 5 ≤ D) (hD : ∀ i, (a.stacks i).length ≤ D) :
    ∃ steps rf, steps ≤ 110 * L + 80 ∧
      Eval (.call HighCountSeed.initializeProgram) steps a (HighCountSeed.initialized a rf) ∧
      StageSpace (.call HighCountSeed.initializeProgram) steps a D := by
  obtain ⟨ns,rs,hns,hes⟩ := seed_eval a L hL
  obtain ⟨nd,rd,ht,_,hp⟩ := HighCountSeed.initialize_trace_space a L D
    (hL 338 (by decide)) hlocal hD
  have hed : Eval (.call HighCountSeed.initializeProgram) nd a (HighCountSeed.initialized a rd) :=
    Eval.call _ ht
  have hsteps := StreamResources.eval_steps_eq 778 777 hes hed
  refine ⟨ns,rs,hns,hes,?_⟩
  rw [hsteps]
  exact ⟨StructuredSpace.call_stack_bound _ _ _ _
    (compiled_site (.call HighCountSeed.initializeProgram) 778 777) ht hp⟩

/-- The actual marked return carries both independent bounds: active-source
time and a maximum prefix cap covering every retained caller word. -/
theorem markedReturn_resources (a : Data) (n L D : ℕ)
    (hcount : BinaryArithmetic.toNat (a.stacks 788) ≤ 2 ^ n)
    (hnL : n + 1 ≤ L) (hnD : n + 1 ≤ D)
    (hL : ∀ i, HashMarkedReturn.kept i = false → (a.stacks i).length ≤ L)
    (hD : ∀ i, (a.stacks i).length ≤ D) (ht : a.stacks 767 = []) :
    ∃ steps, steps + 1 ≤ 3421 * L + 5136 ∧
      Eval HighQueryExecution.markedReturn steps a (HighQueryExecution.returned a) ∧
      Trace (compiled HighQueryExecution.markedReturn 778 777) (steps + 1)
        (a.withPC (some (compiled HighQueryExecution.markedReturn 778 777).entry))
        ((HighQueryExecution.returned a).withPC none) ∧
      StageSpace HighQueryExecution.markedReturn (steps + 1) a (931 * D + 54) := by
  obtain ⟨ns,hns,hes⟩ := markedReturn_eval a n L hcount hnL hL ht
  obtain ⟨nd,hed,_,_,hspace⟩ :=
    HighQueryExecution.markedReturn_trace_space a n D hcount hnD hD ht
  have hsteps := StreamResources.eval_steps_eq 778 777 hes hed
  exact ⟨ns,hns,hes,compiled_halt_trace hes 778 777,by simpa only [hsteps] using hspace⟩

/-- The accepted output has the same actual source-time/all-prefix guarantee;
its entire canonical binary word remains on788. -/
theorem acceptedReturn_resources (a : Data) (n L D : ℕ)
    (hcount : BinaryArithmetic.toNat (a.stacks 788) ≤ 2 ^ n)
    (hnL : n + 1 ≤ L) (hnD : n + 1 ≤ D)
    (hL : ∀ i, HashMarkedReturn.kept i = false → (a.stacks i).length ≤ L)
    (hD : ∀ i, (a.stacks i).length ≤ D) (ht : a.stacks 767 = []) :
    ∃ steps, steps + 1 ≤ 3430 * L + 5147 ∧
      Eval HighQueryExecution.acceptedReturn steps a (HighQueryExecution.accepted a) ∧
      Trace (compiled HighQueryExecution.acceptedReturn 778 777) (steps + 1)
        (a.withPC (some (compiled HighQueryExecution.acceptedReturn 778 777).entry))
        ((HighQueryExecution.accepted a).withPC none) ∧
      StageSpace HighQueryExecution.acceptedReturn (steps + 1) a (931 * D + 54) := by
  obtain ⟨ns,hns,hes⟩ := acceptedReturn_eval a n L hcount hnL hL ht
  obtain ⟨nd,hed,_,_,hspace⟩ :=
    HighQueryExecution.acceptedReturn_trace_space a n D hcount hnD hD ht
  have hsteps := StreamResources.eval_steps_eq 778 777 hes hed
  exact ⟨ns,hns,hes,compiled_halt_trace hes 778 777,by simpa only [hsteps] using hspace⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLocalBounds
