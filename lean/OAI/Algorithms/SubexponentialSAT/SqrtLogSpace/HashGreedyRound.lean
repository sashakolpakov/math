import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateRank

/-! Concrete streamed greedy rounds. The query seam below consists of actual
executions of the fixed attempt command; it must be instantiated by the native
exact-query implementation before an endpoint theorem can use these results. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound

/-- Only the incumbent and two odometer ports vary across candidate boundaries.
The candidate/score ports are restored to the initial empty words. -/
structure Boundary (base : State 40 896) (B C : ℕ) (a : State 40 896) : Prop where
  frame : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 →
    a.stacks i = base.stacks i
  fits : BinaryArgmin.Fits B C (readEntry 770 771 a)

theorem boundary_stable (base : State 40 896) (B C : ℕ) :
    CounterForPrograms.FrameStable counter (fun _ => Boundary base B C) := by
  intro q a b hframe ha
  constructor
  · intro i h0 h1 h2 h3
    rw [← hframe i h2 h3]
    exact ha.frame i h0 h1 h2 h3
  · have hp := hframe 770 (by decide) (by decide)
    have hs := hframe 771 (by decide) (by decide)
    simpa only [readEntry, ← hp, ← hs] using ha.fits

theorem boundary_core (base a : State 40 896) (B C : ℕ)
    (hb : CoreClean base) (ha : Boundary base B C a) : CoreClean a := by
  constructor
  · rw [ha.frame 772 (by decide) (by decide) (by decide) (by decide)]
    exact hb.scratch772
  · rw [ha.frame 773 (by decide) (by decide) (by decide) (by decide)]
    exact hb.scratch773
  · rw [ha.frame 774 (by decide) (by decide) (by decide) (by decide)]
    exact hb.scratch774
  · rw [ha.frame 775 (by decide) (by decide) (by decide) (by decide)]
    exact hb.scratch775
  · rw [ha.frame 776 (by decide) (by decide) (by decide) (by decide)]
    exact hb.queue776

theorem boundary_stored (base a b : State 40 896) (B C : ℕ)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = [])
    (ha : Boundary base B C a) (winner : BinaryArgmin.Entry)
    (hw : BinaryArgmin.Fits B C winner) (hb : b.stacks = stored a winner) :
    Boundary base B C b := by
  constructor
  · intro i h770 h771 h778 h779
    by_cases h768 : i = 768
    · subst i
      simp [hb, stored, h0]
    by_cases h769 : i = 769
    · subst i
      simp [hb, stored, h1]
    simpa [hb, stored, h768, h769, h770, h771] using
      ha.frame i h770 h771 h778 h779
  · simpa [readEntry, hb, stored] using hw

private theorem shape_flatten_length {words : List (List Bool)} {C : ℕ}
    (hw : words.map List.length = [C]) : words.flatten.length = C := by
  have h := congrArg List.sum hw
  simpa [List.length_flatten] using h

/-- Every actual candidate, including losing candidates, pays the attempt and
native comparison costs. No candidate family is allocated in the machine. -/
theorem body_execution (mass : Cmd 40 896) (base : State 40 896)
    (B C attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (hcore : CoreClean base)
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (hattempt : ∀ words a, words.map List.length = [C] → Boundary base B C a →
      a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n a b ∧
        b.stacks = Function.update (Function.update a.stacks 768
          (entry (CounterPrograms.value words.flatten)).payload) 769
          (entry (CounterPrograms.value words.flatten)).score)
    (words : List (List Bool)) (a : State 40 896)
    (hw : words.map List.length = [C]) (ha : Boundary base B C a)
    (hcounter : a.stacks 778 = Encoding.encodeList id words) (hscratch : a.stacks 779 = []) :
    ∃ n ≤ attemptCost + (100 * (B + C + 1) + 1), ∃ b,
      Eval (body mass) n a b ∧
      b.stacks = stored a (BinaryArgmin.pick (readEntry 770 771 a)
        (entry (CounterPrograms.value words.flatten))) := by
  have hrank : CounterPrograms.value words.flatten < 2 ^ C := by
    simpa only [shape_flatten_length hw] using
      ExecCNFTupleOdometer.value_lt_power_length words.flatten
  obtain ⟨n, hn, b, he, hb⟩ := hattempt words a hw ha hcounter hscratch
  obtain ⟨t, ht, c, hc, hs⟩ := body_eval_of_attempt mass a b n B C
    (entry (CounterPrograms.value words.flatten)) he hb
    (boundary_core base a B C hcore ha) (hfit _ hrank) ha.fits
  exact ⟨t, by omega, c, hc, hs⟩

/-- Instantiate the real finite iterator from the paid native attempt traces.
The only changing stored values are the incumbent and bounded odometer. -/
theorem body_spec (mass : Cmd 40 896) (base : State 40 896)
    (B C attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (hattempt : ∀ words a, words.map List.length = [C] → Boundary base B C a →
      a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n a b ∧
        b.stacks = Function.update (Function.update a.stacks 768
          (entry (CounterPrograms.value words.flatten)).payload) 769
          (entry (CounterPrograms.value words.flatten)).score) :
    ExecCNFTupleEnumeration.BodySpec counter (body mass) [C] (Boundary base B C)
      (attemptCost + (100 * (B + C + 1) + 1)) := by
  intro words a hw ha hc hs
  obtain ⟨n, hn, b, he, hb⟩ := body_execution mass base B C attemptCost entry hcore
    hfit hattempt words a hw ha hc hs
  have hrank : CounterPrograms.value words.flatten < 2 ^ C := by
    simpa only [shape_flatten_length hw] using
      ExecCNFTupleOdometer.value_lt_power_length words.flatten
  refine ⟨n, b, hn, he, ?_, ?_, ?_⟩
  · simpa [hb, stored, counter] using hc
  · simpa [hb, stored, counter] using hs
  · exact boundary_stored base a b B C h0 h1 ha _
      (BinaryArgmin.pick_fits ha.fits (hfit _ hrank)) hb

/-- Determinism identifies every actual update trace with the measured native
one, including its restored scratch and the next odometer boundary. -/
theorem body_refines (mass : Cmd 40 896) (base : State 40 896)
    (B C attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (hattempt : ∀ words a, words.map List.length = [C] → Boundary base B C a →
      a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n a b ∧
        b.stacks = Function.update (Function.update a.stacks 768
          (entry (CounterPrograms.value words.flatten)).payload) 769
          (entry (CounterPrograms.value words.flatten)).score)
    (words : List (List Bool)) (a b : State 40 896) (n : ℕ)
    (hw : words.map List.length = [C]) (hc : a.stacks 778 = Encoding.encodeList id words)
    (he : Eval (body mass) n a b) (ha : Boundary base B C a) (hs : a.stacks 779 = []) :
    readEntry 770 771 b = BinaryArgmin.pick (readEntry 770 771 a)
      (entry (CounterPrograms.value words.flatten)) ∧
      Boundary base B C (ExecCNFTupleEnumeration.advanceResult counter b words) ∧
      (ExecCNFTupleEnumeration.advanceResult counter b words).stacks 779 = [] := by
  obtain ⟨t, _, c, ht, hout⟩ := body_execution mass base B C attemptCost entry hcore
    hfit hattempt words a hw ha hc hs
  have hbc : b = c := he.final_unique 778 ht
  subst c
  have hrank : CounterPrograms.value words.flatten < 2 ^ C := by
    simpa only [shape_flatten_length hw] using
      ExecCNFTupleOdometer.value_lt_power_length words.flatten
  have hb := boundary_stored base a b B C h0 h1 ha _
    (BinaryArgmin.pick_fits ha.fits (hfit _ hrank)) hout
  refine ⟨?_, boundary_stable base B C 0 b _
    (ExecCNFTupleEnumeration.advanceResult_outside counter b words) hb, ?_⟩
  · simp [readEntry, hout, stored]
  · exact ExecCNFTupleEnumeration.advanceResult_scratch counter b words

/-- The complete native scan returns an attained minimum, preserves every
fixed caller word, and resets the singleton counter for the next round. -/
theorem scan_minimum (mass : Cmd 40 896) (base : State 40 896)
    (B C attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hcounter : base.stacks 778 = Encoding.encodeList id [List.replicate C false])
    (hscratch : base.stacks 779 = []) (hseed : readEntry 770 771 base = entry 0)
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (hattempt : ∀ words a, words.map List.length = [C] → Boundary base B C a →
      a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n a b ∧
        b.stacks = Function.update (Function.update a.stacks 768
          (entry (CounterPrograms.value words.flatten)).payload) 769
          (entry (CounterPrograms.value words.flatten)).score) :
    ∃ n ≤ 2 ^ C * (attemptCost + (100 * (B + C + 1) + 1) + 7 * (2 * C + 3) + 5) + 2,
      ∃ b, Eval (ExecCNFTupleEnumeration.enumerate counter (body mass)) n base b ∧
        Boundary base B C b ∧ b.stacks 779 = [] ∧
        b.stacks 778 = Encoding.encodeList id [List.replicate C false] ∧
        (∃ j < 2 ^ C, readEntry 770 771 b = entry j) ∧
        (∀ j < 2 ^ C, BinaryArgmin.value (readEntry 770 771 b) ≤ BinaryArgmin.value (entry j)) ∧
        readEntry 770 771 b = HashSelect.best BinaryArgmin.value (entry 0)
          ((List.range' 0 (2 ^ C)).map entry) := by
  have hi : Boundary base B C base := by
    refine ⟨fun _ _ _ _ _ => rfl, ?_⟩
    rw [hseed]
    exact hfit 0 (pow_pos (by decide) _)
  have spec := body_spec mass base B C attemptCost entry h0 h1 hcore hfit hattempt
  obtain ⟨n, b, he, hv, hb, _, hscratch', hn⟩ :=
    ExecCNFTupleEnumeration.enumerate_correct counter (body mass) [C] (Boundary base B C)
      (attemptCost + (100 * (B + C + 1) + 1)) (boundary_stable base B C) spec
      [List.replicate C false] base (by simp) hi hcounter hscratch
      (by simp)
  have hstart : Boundary base B C (ExecCNFTupleEnumeration.startResult counter base) :=
    boundary_stable base B C 0 base _ (fun _ _ _ => rfl) hi
  have hrefine : ∀ words a b nb, words.map List.length = [C] →
      a.stacks counter.counter = Encoding.encodeList id words → Eval (body mass) nb a b →
      (Boundary base B C a ∧ a.stacks 779 = []) →
      readEntry 770 771 b = BinaryArgmin.pick (readEntry 770 771 a)
        (entry (CounterPrograms.value words.flatten)) ∧
      (Boundary base B C (ExecCNFTupleEnumeration.advanceResult counter b words) ∧
        (ExecCNFTupleEnumeration.advanceResult counter b words).stacks 779 = []) := by
    intro words a b nb hw hc he ha
    exact body_refines mass base B C attemptCost entry h0 h1 hcore hfit hattempt
      words a b nb hw hc he ha.1 ha.2
  obtain ⟨hmem, hmin⟩ := visits_minimum counter (body mass) [C] 770 771 entry
    (fun a => Boundary base B C a ∧ a.stacks 779 = [])
    (by decide) (by decide) (by decide) (by decide) hrefine hv
    ⟨hstart, hscratch⟩
  have hbest := visits_best counter (body mass) [C] 770 771 entry
    (fun a => Boundary base B C a ∧ a.stacks 779 = [])
    (by decide) (by decide) (by decide) (by decide) hrefine hv
    ⟨hstart, hscratch⟩
  have hreset := Enumerators.visits_reset_counter hv
    (ExecCNFTupleEnumeration.startResult_flag counter base)
  have hflat : ([List.replicate C false] : List (List Bool)).flatten.length = C := by simp
  rw [hflat] at hn hmem hmin hbest
  change readEntry 770 771 b ∈ readEntry 770 771 base :: _ at hmem
  change readEntry 770 771 b = HashSelect.best BinaryArgmin.value
    (readEntry 770 771 base) _ at hbest
  rw [hseed] at hmem hbest
  refine ⟨1 + n, ?_, b, he, hb, hscratch', ?_, ?_, ?_, hbest⟩
  · simpa [Encoding.encodeList, Encoding.length_frame] using hn
  · change b.stacks counter.counter = Encoding.encodeList id [List.replicate C false]
    exact hreset
  · rcases List.mem_cons.mp hmem with hfirst | hrest
    · exact ⟨0, pow_pos (by decide) _, hfirst⟩
    · obtain ⟨j, hj, heq⟩ := List.mem_map.mp hrest
      exact ⟨j, by simpa using hj, heq.symm⟩
  · intro j hj
    exact hmin j (by simpa using hj)

/-- One complete fixed native round: paid seed, all candidate visits, native
comparison, one attained winner append, and charged outer flag restoration.
The mathematical range in the conclusion records the trace; it is not stored. -/
theorem round_minimum (mass : Cmd 40 896) (a : State 40 896)
    (B C attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (h0 : a.stacks 768 = []) (h1 : a.stacks 769 = []) (hcore : CoreClean a)
    (hbp : a.stacks 770 = []) (hbs : a.stacks 771 = [])
    (hcounter : a.stacks 778 = Encoding.encodeList id [List.replicate C false])
    (hscratch : a.stacks 779 = [])
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (hattempt : ∀ words d, words.map List.length = [C] →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i) →
      d.stacks 778 = Encoding.encodeList id words → d.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n d b ∧
        b.stacks = Function.update (Function.update d.stacks 768
          (entry (CounterPrograms.value words.flatten)).payload) 769
          (entry (CounterPrograms.value words.flatten)).score) :
    ∃ n ≤ roundBudget attemptCost B C, ∃ b : State 40 896, ∃ winner : BinaryArgmin.Entry,
      Eval (round mass) n a b ∧
      b.stacks = Function.update a.stacks 777
        (true :: (Encoding.frame winner.payload.reverse ++ a.stacks 777)) ∧
      b.regs 9 = true ∧ BinaryArgmin.Fits B C winner ∧
      (∃ j < 2 ^ C, winner = entry j) ∧
      (∀ j < 2 ^ C, BinaryArgmin.value winner ≤ BinaryArgmin.value (entry j)) ∧
      winner = HashSelect.best BinaryArgmin.value (entry 0)
        ((List.range' 0 (2 ^ C)).map entry) := by
  have hpositive : 0 < 2 ^ C := pow_pos (by decide) _
  obtain ⟨na, hna, first, hea, hfirst⟩ := hattempt [List.replicate C false] a
    (by simp) (fun _ _ _ _ _ => rfl) hcounter hscratch
  have hfirst' : first.stacks = Function.update (Function.update a.stacks 768
      (entry 0).payload) 769 (entry 0).score := by
    simpa [CounterPrograms.value] using hfirst
  have hcore' : CoreClean first := by
    constructor <;> simp [hfirst', hcore.scratch772, hcore.scratch773,
      hcore.scratch774, hcore.scratch775, hcore.queue776]
  have hentry : readEntry 768 769 first = entry 0 := by simp [readEntry, hfirst']
  obtain ⟨ni, hni, seed, hei, hseed⟩ := NativeRound.install_eval first B C hcore'
    (by simp [hfirst', hbp]) (by simp [hfirst', hbs]) (by simpa only [hentry] using hfit 0 hpositive)
  have hseed' : seed.stacks = stored first (entry 0) := by simpa only [hentry] using hseed
  have hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 →
      seed.stacks i = a.stacks i := by
    intro i h770 h771 h778 h779
    by_cases h768 : i = 768
    · subst i
      simp [hseed', stored, h0]
    by_cases h769 : i = 769
    · subst i
      simp [hseed', stored, h1]
    simp [hseed', stored, hfirst', h768, h769, h770, h771]
  have hs0 : seed.stacks 768 = [] := by simp [hseed', stored]
  have hs1 : seed.stacks 769 = [] := by simp [hseed', stored]
  have hsCore : CoreClean seed := by
    constructor
    · rw [hframe 772 (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch772
    · rw [hframe 773 (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch773
    · rw [hframe 774 (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch774
    · rw [hframe 775 (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch775
    · rw [hframe 776 (by decide) (by decide) (by decide) (by decide)]
      exact hcore.queue776
  have hsCounter : seed.stacks 778 = Encoding.encodeList id [List.replicate C false] := by
    simp [hseed', stored, hfirst', hcounter]
  have hsScratch : seed.stacks 779 = [] := by simp [hseed', stored, hfirst', hscratch]
  have hsEntry : readEntry 770 771 seed = entry 0 := by simp [readEntry, hseed', stored]
  obtain ⟨ns, hns, final, hes, hfinal, hfScratch, hfCounter, hmem, hmin, hbest⟩ :=
    scan_minimum mass seed B C attemptCost entry hs0 hs1 hsCore hsCounter hsScratch hsEntry hfit
      (fun words d hw hd hc hs => hattempt words d hw
        (fun i h770 h771 h778 h779 => (hd.frame i h770 h771 h778 h779).trans
          (hframe i h770 h771 h778 h779)) hc hs)
  obtain ⟨after, hep, hafter⟩ := NativeRound.append_eval final
  let winner := readEntry 770 771 final
  have hfinalFrame : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 →
      final.stacks i = a.stacks i := by
    intro i h770 h771 h778 h779
    exact (hfinal.frame i h770 h771 h778 h779).trans (hframe i h770 h771 h778 h779)
  have hp : 5 * (final.stacks 770).length + 2 * (final.stacks 771).length + 11 ≤
      5 * C + 2 * B + 11 := by
    have hfitFinal := hfinal.fits
    rcases hfitFinal with ⟨hs, hp⟩
    dsimp only [readEntry] at hs hp
    omega
  refine ⟨na + (ni + (ns + (5 * (final.stacks 770).length +
    2 * (final.stacks 771).length + 11 + 1))),
    round_cost_le attemptCost B C _ _ _ _ hna hni hns hp,
    guardSet after, winner, ?_, ?_, by simp [guardSet], hfinal.fits, hmem, hmin, hbest⟩
  · exact round_eval_of_stages mass a first seed final after na ni ns
      (5 * (final.stacks 770).length + 2 * (final.stacks 771).length + 11) hea hei hes hep
  · change after.stacks = _
    rw [hafter]
    funext i
    by_cases h770 : i = 770
    · subst i
      simp [appendedStacks, hbp]
    by_cases h771 : i = 771
    · subst i
      simp [appendedStacks, hbs]
    by_cases h777 : i = 777
    · subst i
      simp [appendedStacks, winner, readEntry,
        hfinalFrame 777 (by decide) (by decide) (by decide) (by decide)]
    by_cases h778 : i = 778
    · subst i
      simp [appendedStacks, hfCounter, hcounter]
    by_cases h779 : i = 779
    · subst i
      simp [appendedStacks, hfScratch, hscratch]
    simp [appendedStacks, h770, h771, h777,
      hfinalFrame i h770 h771 h778 h779]

/-- Proof-level name for the deterministic cached minimum. The finite machine
uses its binary counter and two entries, not this mathematical recursion. -/
def chosenEntry (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (rows : List (List Bool)) : BinaryArgmin.Entry :=
  (HashGreedy.scan BinaryArgmin.value (entry rows) (2 ^ C - 1)).1

theorem chosenEntry_eq_best (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (rows : List (List Bool)) :
    chosenEntry entry C rows = HashSelect.best BinaryArgmin.value (entry rows 0)
      ((List.range' 0 (2 ^ C)).map (entry rows)) := by
  have hp : 1 ≤ 2 ^ C := by have := pow_pos (by decide : 0 < (2 : ℕ)) C; omega
  simpa only [chosenEntry, Nat.sub_add_cancel hp] using
    HashGreedy.scan_eq_best BinaryArgmin.value (entry rows) (2 ^ C - 1)

def nextRows (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (rows : List (List Bool)) : List (List Bool) :=
  (chosenEntry entry C rows).payload :: rows

/-- The history and remaining unary count are the only words changed by outer
round control. All other retained parameters keep their literal contents. -/
structure RowBoundary (base : State 40 896) (rows : List (List Bool))
    (a : State 40 896) : Prop where
  frame : ∀ i : Fin 896, i ≠ 777 → i ≠ 781 → a.stacks i = base.stacks i
  history : a.stacks 777 = encodedHistory rows

theorem rowBoundary_read (base a : State 40 896) (rows : List (List Bool))
    (ha : RowBoundary base rows a) :
    RowBoundary base rows (HashSelectProgram.readCounterState outer a) := by
  constructor
  · intro i h777 h781
    simpa [HashSelectProgram.readCounterState, outer, h781] using ha.frame i h777 h781
  · simpa [HashSelectProgram.readCounterState, outer] using ha.history

theorem rowBoundary_round (base a b : State 40 896) (rows : List (List Bool))
    (entry : List (List Bool) → ℕ → BinaryArgmin.Entry) (C : ℕ)
    (ha : RowBoundary base rows a)
    (hb : b.stacks = Function.update a.stacks 777
      (true :: (Encoding.frame (chosenEntry entry C rows).payload.reverse ++ a.stacks 777))) :
    RowBoundary base (nextRows entry C rows) b := by
  constructor
  · intro i h777 h781
    simpa [hb, h777] using ha.frame i h777 h781
  · simp [hb, ha.history, encodedHistory, nextRows, Encoding.encodeList]

/-- Actual unary-controlled iteration of complete native rounds, with literal
history serialization and exact caller-frame preservation. The query cost is
needed only at the bounded histories that this execution can reach. -/
theorem rounds_history (mass : Cmd 40 896) (base : State 40 896)
    (B C attemptCost count : ℕ) (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (initial : List (List Bool)) (hhistory : base.stacks 777 = encodedHistory initial)
    (hdepth : (base.stacks 781).length = count)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hbp : base.stacks 770 = []) (hbs : base.stacks 771 = [])
    (hcounter : base.stacks 778 = Encoding.encodeList id [List.replicate C false])
    (hscratch : base.stacks 779 = [])
    (hfit : ∀ rows, rows.length ≤ initial.length + count →
      ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry rows j))
    (hattempt : ∀ rows a, rows.length ≤ initial.length + count → RowBoundary base rows a →
      (∃ q ≤ count, rows = HashSelectProgram.iter (nextRows entry C) q initial) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length + count * (2 * C + 2) →
      ∀ words d, words.map List.length = [C] →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i) →
      d.stacks 778 = Encoding.encodeList id words → d.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n d b ∧
        b.stacks = Function.update (Function.update d.stacks 768
          (entry rows (CounterPrograms.value words.flatten)).payload) 769
          (entry rows (CounterPrograms.value words.flatten)).score) :
    ∃ n ≤ HashSelectProgram.roundsBudget (roundBudget attemptCost B C) count, ∃ b,
      Eval (NativeRound.rounds mass) n base b ∧
      RowBoundary base (HashSelectProgram.iter (nextRows entry C) count initial) b ∧
      b.stacks 781 = [] ∧ b.regs 9 = false := by
  let invariant := fun q rows a => RowBoundary base rows a ∧ rows.length = initial.length + q ∧
    rows = HashSelectProgram.iter (nextRows entry C) q initial ∧
    (encodedHistory rows).length ≤ (encodedHistory initial).length + q * (2 * C + 2)
  have spec : HashSelectProgram.BoundedRoundSpec outer (round mass) (nextRows entry C)
      invariant (roundBudget attemptCost B C) count := by
    constructor
    · intro q rows a ha
      exact ⟨rowBoundary_read base a rows ha.1, ha.2⟩
    · intro q rows a hq ha hflag
      have hlen : rows.length ≤ initial.length + count := by
        have hh := ha.2.1
        omega
      have hbytes : (encodedHistory rows).length ≤
          (encodedHistory initial).length + count * (2 * C + 2) :=
        ha.2.2.2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hq.le) _)
      have hf := ha.1.frame
      have hcoreA : CoreClean a := by
        constructor
        · rw [hf 772 (by decide) (by decide)]
          exact hcore.scratch772
        · rw [hf 773 (by decide) (by decide)]
          exact hcore.scratch773
        · rw [hf 774 (by decide) (by decide)]
          exact hcore.scratch774
        · rw [hf 775 (by decide) (by decide)]
          exact hcore.scratch775
        · rw [hf 776 (by decide) (by decide)]
          exact hcore.queue776
      obtain ⟨n, hn, b, winner, he, hb, hguard, hwfit, _, _, hbest⟩ :=
        round_minimum mass a B C attemptCost (entry rows)
          ((hf 768 (by decide) (by decide)).trans h0)
          ((hf 769 (by decide) (by decide)).trans h1) hcoreA
          ((hf 770 (by decide) (by decide)).trans hbp)
          ((hf 771 (by decide) (by decide)).trans hbs)
          ((hf 778 (by decide) (by decide)).trans hcounter)
          ((hf 779 (by decide) (by decide)).trans hscratch)
          (hfit rows hlen) (hattempt rows a hlen ha.1 ⟨q,hq.le,ha.2.2.1⟩ hbytes)
      have hwinner : winner = chosenEntry entry C rows :=
        hbest.trans (chosenEntry_eq_best entry C rows).symm
      rw [hwinner] at hb
      refine ⟨n, hn, b, ⟨rowBoundary_round base a b rows entry C ha.1 hb, ?_, ?_, ?_⟩,
        ?_, hguard, he⟩
      · dsimp only [nextRows]
        simp only [List.length_cons, ha.2.1]
        omega
      · rw [HashSelectProgram.iter_succ_apply, ← ha.2.2.1]
      · have hlenNext : (encodedHistory (nextRows entry C rows)).length =
            (encodedHistory rows).length + 2 * (chosenEntry entry C rows).payload.length + 2 := by
          simp [encodedHistory, nextRows, Encoding.encodeList, Encoding.length_frame]
          omega
        rw [hlenNext, Nat.succ_mul q (2 * C + 2)]
        rw [hwinner] at hwfit
        have hh := ha.2.2.2
        have hw := hwfit.2
        omega
      · simp [hb, outer]
  have hi : invariant 0 initial base := ⟨⟨fun _ _ _ => rfl, hhistory⟩, by simp, rfl, by simp⟩
  obtain ⟨n, hn, b, hb, hcounter', hflag, he⟩ :=
    HashSelectProgram.rounds_eval_bounded outer (round mass) (nextRows entry C) invariant
      (roundBudget attemptCost B C) count spec 0 initial (base.stacks 781) base
      (by simp [hdepth]) hi rfl
  refine ⟨n, by simpa only [hdepth] using hn, b, he, ?_, hcounter', hflag⟩
  simpa only [hdepth] using hb.1

theorem chosenEntry_mem (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (rows : List (List Bool)) :
    ∃ j < 2 ^ C, chosenEntry entry C rows = entry rows j := by
  have hm := HashSelect.best_mem BinaryArgmin.value (entry rows 0)
    ((List.range' 0 (2 ^ C)).map (entry rows))
  rw [← chosenEntry_eq_best] at hm
  rcases List.mem_cons.mp hm with hzero | hrest
  · exact ⟨0, pow_pos (by decide) _, hzero⟩
  · obtain ⟨j, hj, he⟩ := List.mem_map.mp hrest
    exact ⟨j, by simpa using hj, he.symm⟩

theorem chosenEntry_le (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (rows : List (List Bool)) (j : ℕ) (hj : j < 2 ^ C) :
    BinaryArgmin.value (chosenEntry entry C rows) ≤ BinaryArgmin.value (entry rows j) := by
  rw [chosenEntry_eq_best]
  exact HashSelect.best_le_member _ _ _ _ (List.mem_map.mpr ⟨j, by simpa using hj, rfl⟩)

theorem chosenEntry_fits (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (B C : ℕ) (rows : List (List Bool))
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry rows j)) :
    BinaryArgmin.Fits B C (chosenEntry entry C rows) := by
  obtain ⟨j, hj, he⟩ := chosenEntry_mem entry C rows
  rw [he]
  exact hfit j hj

theorem iter_length (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (initial : List (List Bool)) (q : ℕ) :
    (HashSelectProgram.iter (nextRows entry C) q initial).length = initial.length + q := by
  induction q with
  | zero => simp [HashSelectProgram.iter]
  | succ q ih =>
    rw [HashSelectProgram.iter_succ_apply]
    simp [nextRows, ih, Nat.add_assoc]

/-- The physical serialized history grows only by the selected bounded row.
The exponentially many losing payloads never contribute to this retained word. -/
theorem encodedHistory_iter_length_le
    (entry : List (List Bool) → ℕ → BinaryArgmin.Entry) (B C count : ℕ)
    (initial : List (List Bool))
    (hfit : ∀ rows, rows.length ≤ initial.length + count →
      ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry rows j)) :
    ∀ q ≤ count,
      (encodedHistory (HashSelectProgram.iter (nextRows entry C) q initial)).length ≤
        (encodedHistory initial).length + q * (2 * C + 2) := by
  intro q
  induction q with
  | zero => simp [HashSelectProgram.iter]
  | succ q ih =>
    intro hq
    have hi := ih (by omega)
    have hfitChosen := chosenEntry_fits entry B C
      (HashSelectProgram.iter (nextRows entry C) q initial)
      (hfit _ (by rw [iter_length]; omega))
    have hbytes := hfitChosen.2
    rw [HashSelectProgram.iter_succ_apply]
    have hlen : (encodedHistory (nextRows entry C
        (HashSelectProgram.iter (nextRows entry C) q initial))).length =
        (encodedHistory (HashSelectProgram.iter (nextRows entry C) q initial)).length +
          2 * (chosenEntry entry C (HashSelectProgram.iter (nextRows entry C) q initial)).payload.length + 2 := by
      simp [encodedHistory, nextRows, Encoding.encodeList, Encoding.length_frame]
      omega
    rw [hlen, Nat.succ_mul q (2 * C + 2)]
    omega

theorem iter_accepts_initial {X : Type*} (rowAccept : List Bool → X → Bool)
    (entry : List (List Bool) → ℕ → BinaryArgmin.Entry) (C : ℕ)
    (initial : List (List Bool)) (q : ℕ) (x : X) :
    HashSelect.accepts rowAccept (HashSelectProgram.iter (nextRows entry C) q initial) x = true →
      HashSelect.accepts rowAccept initial x = true := by
  induction q with
  | zero => exact id
  | succ q ih =>
    rw [HashSelectProgram.iter_succ_apply]
    intro hx
    exact ih (Bool.and_eq_true_iff.mp hx).2

/-- Contraction averages over the original reference family. Extra decoded
binary candidates can repeat rows without changing the argument. -/
theorem chosen_contraction {X : Type*} [Fintype X] {c : ℕ}
    (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
    (entry : List (List Bool) → ℕ → BinaryArgmin.Entry) (C : ℕ)
    (rows : List (List Bool)) (family : Fin (c + 1) → List Bool)
    (hsound : ∀ j < 2 ^ C, BinaryArgmin.value (entry rows j) =
      HashSelect.mass rowAccept weight ((entry rows j).payload :: rows))
    (hcover : ∀ i, ∃ j < 2 ^ C, (entry rows j).payload = family i)
    (hcoverage : ∀ x, HashSelect.accepts rowAccept rows x = true → 0 < weight x →
      3 * HashSelect.survivingCandidates rowAccept family x ≤ 2 * (c + 1)) :
    3 * HashSelect.mass rowAccept weight (nextRows entry C rows) ≤
      2 * HashSelect.mass rowAccept weight rows := by
  have hchosen : BinaryArgmin.value (chosenEntry entry C rows) =
      HashSelect.mass rowAccept weight (nextRows entry C rows) := by
    obtain ⟨j, hj, he⟩ := chosenEntry_mem entry C rows
    simpa only [nextRows, he] using hsound j hj
  apply HashGreedy.contraction_of_minimum rowAccept weight family rows
    (chosenEntry entry C rows).payload
  · intro i
    obtain ⟨j, hj, he⟩ := hcover i
    have hm := chosenEntry_le entry C rows j hj
    rw [hchosen, hsound j hj, he] at hm
    exact hm
  · exact hcoverage

/-- The deterministic rows serialized by the actual outer run have zero
violation mass at the supplied original square-root-log loop cap. -/
theorem iter_mass_zero {X : Type*} [Fintype X] {c : ℕ}
    (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
    (entry : List (List Bool) → ℕ → BinaryArgmin.Entry) (C : ℕ)
    (family : Fin (c + 1) → List Bool) (initial : List (List Bool)) (n m : ℕ)
    (hx : Fintype.card X ≤ 2 ^ n) (hw : ∀ x, weight x ≤ m)
    (hsound : ∀ q < HashSelect.loopCap n m, ∀ j < 2 ^ C,
      BinaryArgmin.value (entry (HashSelectProgram.iter (nextRows entry C) q initial) j) =
      HashSelect.mass rowAccept weight
        ((entry (HashSelectProgram.iter (nextRows entry C) q initial) j).payload ::
          HashSelectProgram.iter (nextRows entry C) q initial))
    (hcover : ∀ q < HashSelect.loopCap n m, ∀ i, ∃ j < 2 ^ C,
      (entry (HashSelectProgram.iter (nextRows entry C) q initial) j).payload = family i)
    (hcoverage : ∀ x, HashSelect.accepts rowAccept initial x = true → 0 < weight x →
      3 * HashSelect.survivingCandidates rowAccept family x ≤ 2 * (c + 1)) :
    HashSelect.mass rowAccept weight
      (HashSelectProgram.iter (nextRows entry C) (HashSelect.loopCap n m) initial) = 0 := by
  apply HashSelect.zero_of_contraction
    (fun q => HashSelect.mass rowAccept weight (HashSelectProgram.iter (nextRows entry C) q initial))
    (n + Nat.size m + 1)
  · intro q hq
    rw [HashSelectProgram.iter_succ_apply]
    apply chosen_contraction rowAccept weight entry C _ family (hsound q hq) (hcover q hq)
    intro x ha hp
    exact hcoverage x (iter_accepts_initial rowAccept entry C initial q x ha) hp
  · exact HashSelect.initial_mass_lt_cap_power rowAccept weight initial n m hx hw

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound
