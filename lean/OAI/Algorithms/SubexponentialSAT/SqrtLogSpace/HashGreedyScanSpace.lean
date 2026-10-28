import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound

/-! Uniform storage for the actual streamed candidate scan. The attempt
premises describe executions and prefixes of the fixed preparation/query/padding
command; the complete query implementation must instantiate them. No bound in
this module uses the number of candidates as a space bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound

theorem boundary_stack_bound (base a : State 40 896) (B C L : ℕ)
    (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hB : B ≤ L) (hC : C ≤ L) (hcounter : 2 * C + 3 ≤ L)
    (ha : Boundary base B C a) (hs : a.stacks 779 = [])
    (hc : (a.stacks 778).length = 2 * C + 3) :
    ∀ i, (a.stacks i).length ≤ L := by
  intro i
  by_cases h770 : i = 770
  · subst i
    exact ha.fits.2.trans hC
  by_cases h771 : i = 771
  · subst i
    exact ha.fits.1.le.trans hB
  by_cases h778 : i = 778
  · subst i
    exact hc.le.trans hcounter
  by_cases h779 : i = 779
  · subst i
    simp [hs]
  rw [ha.frame i h770 h771 h778 h779]
  exact hbase i

/-- Only the local native comparison time is used to bound comparison
workspace. The potentially expensive attempt has its independent prefix bound. -/
theorem body_space (mass : Cmd 40 896) (base a : State 40 896)
    (B C L K attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (hcore : CoreClean base)
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (words : List (List Bool)) (hw : words.map List.length = [C])
    (ha : Boundary base B C a) (hL : ∀ i, (a.stacks i).length ≤ L)
    (hB : B ≤ L) (hC : C ≤ L)
    (hattempt : ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n a b ∧
      b.stacks = Function.update (Function.update a.stacks 768
        (entry (CounterPrograms.value words.flatten)).payload) 769
        (entry (CounterPrograms.value words.flatten)).score)
    (hspace : ∀ n b, Eval (attempt mass) n a b → StageSpace (attempt mass) n a K)
    {steps : ℕ} {b : State 40 896} (he : Eval (body mass) steps a b) :
    StageSpace (body mass) steps a (max K (896 * L + 100 * (B + C + 1) + 1)) := by
  have hlen : words.flatten.length = C := by
    have h := congrArg List.sum hw
    simpa [List.length_flatten] using h
  have hrank : CounterPrograms.value words.flatten < 2 ^ C := by
    simpa only [hlen] using ExecCNFTupleOdometer.value_lt_power_length words.flatten
  have hentry := hfit _ hrank
  obtain ⟨na, _, first, hfirst, hout⟩ := hattempt
  change Eval (.seq (attempt mass) (HashSelectProgram.update core)) steps a b at he
  cases he with
  | @seq _ _ n m a middle b hn hm =>
    have hmid : middle.stacks = Function.update (Function.update a.stacks 768
        (entry (CounterPrograms.value words.flatten)).payload) 769
        (entry (CounterPrograms.value words.flatten)).score := by
      rw [hn.final_unique 778 hfirst]
      exact hout
    have hmidBound : ∀ i, (middle.stacks i).length ≤ L := by
      intro i
      by_cases h768 : i = 768
      · subst i
        simpa [hmid] using hentry.2.trans hC
      by_cases h769 : i = 769
      · subst i
        simpa [hmid] using hentry.1.le.trans hB
      simpa [hmid, h768, h769] using hL i
    have hclean := boundary_core base a B C hcore ha
    have hmidClean : CoreClean middle := by
      constructor <;> simp [hmid, hclean.scratch772, hclean.scratch773,
        hclean.scratch774, hclean.scratch775, hclean.queue776]
    obtain ⟨nu, hnu, last, hu, _⟩ := update_eval middle B C hmidClean
      (by simpa [readEntry, hmid] using hentry)
      (by simpa [readEntry, hmid] using ha.fits)
    have hmBound : m ≤ 100 * (B + C + 1) + 1 := by
      rw [StreamResources.eval_steps_eq 778 777 hm hu]
      exact hnu
    have hupdate : StageSpace (HashSelectProgram.update core) m middle
        (max K (896 * L + 100 * (B + C + 1) + 1)) := by
      constructor
      intro k c hk ht i
      have hinitial : dataBits (middle.withPC
          (some (compiled (HashSelectProgram.update core) 778 777).entry)) ≤ 896 * L :=
        StreamResources.dataBits_le_mul _ hmidBound
      have hp := StructuredSpace.local_stack_bound
        (compiled (HashSelectProgram.update core) 778 777)
        (steps := 100 * (B + C + 1) + 1) hinitial k c (hk.trans hmBound) ht i
      exact hp.trans (by simpa only [Nat.add_assoc] using
        (Nat.le_max_right K (896 * L + 100 * (B + C + 1) + 1)))
    apply StageSpace.seq hn hm _ hupdate
    constructor
    intro k c hk ht i
    exact ((hspace n middle hn).bound k c hk ht i).trans (Nat.le_max_left _ _)

/-- Every callback and increment of the real scan shares this bound, including
the last overflowing increment. The cardinality of the scan is absent. -/
theorem visits_space (mass : Cmd 40 896) (base : State 40 896)
    (B C L K attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hB : B ≤ L) (hC : C ≤ L) (hcounter : 2 * C + 3 ≤ L)
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (hattempt : ∀ words a, words.map List.length = [C] → Boundary base B C a →
      a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n a b ∧
        b.stacks = Function.update (Function.update a.stacks 768
          (entry (CounterPrograms.value words.flatten)).payload) 769
          (entry (CounterPrograms.value words.flatten)).score)
    (hspace : ∀ words a n b, words.map List.length = [C] → Boundary base B C a →
      a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
      Eval (attempt mass) n a b → StageSpace (attempt mass) n a K)
    {ranks : List ℕ} {steps : ℕ} {a b : State 40 896}
    (hvis : ExecCNFTupleEnumeration.Visits counter (body mass) [C] ranks steps a b)
    (ha : Boundary base B C a) (hs : a.stacks 779 = [])
    (hc : (a.stacks 778).length = 2 * C + 3) :
    ∀ k c, k ≤ steps →
      Trace (compiled (ExecCNFTupleEnumeration.loopCmd counter (body mass)) 778 778) k
        (a.withPC (some (compiled
          (ExecCNFTupleEnumeration.loopCmd counter (body mass)) 778 778).entry)) c →
      ∀ i, (c.stacks i).length ≤
        max K (896 * L + 100 * (B + C + 1) + 7 * (2 * C + 3) + 20) := by
  let I := fun a : State 40 896 => Boundary base B C a ∧ a.stacks 779 = [] ∧
    (a.stacks 778).length = 2 * C + 3
  have hbound : ∀ a, I a → ∀ i, (a.stacks i).length ≤ L := by
    intro a hi
    exact boundary_stack_bound base a B C L hbase hB hC hcounter hi.1 hi.2.1 hi.2.2
  have hcallback : ∀ words a b nb, words.map List.length = [C] →
      a.stacks counter.counter = Encoding.encodeList id words →
      Eval (body mass) nb a b → I a → a.regs (counter.register 2) = true →
      I b ∧ b.stacks counter.scratch = [] ∧
      ∀ k c, k ≤ nb → Trace (compiled (body mass) counter.counter counter.counter) k
        (a.withPC (some (compiled (body mass) counter.counter counter.counter).entry)) c →
        ∀ i, (c.stacks i).length ≤ max K (896 * L + 100 * (B + C + 1) + 1) := by
    intro words a b nb hw hc he hi _
    obtain ⟨n, _, d, hd, hout⟩ := body_execution mass base B C attemptCost entry hcore
      hfit hattempt words a hw hi.1 hc hi.2.1
    have hb : b.stacks = stored a (BinaryArgmin.pick (readEntry 770 771 a)
        (entry (CounterPrograms.value words.flatten))) := by
      rw [he.final_unique 778 hd]
      exact hout
    have hlen : words.flatten.length = C := by
      have h := congrArg List.sum hw
      simpa [List.length_flatten] using h
    have hrank : CounterPrograms.value words.flatten < 2 ^ C := by
      simpa only [hlen] using ExecCNFTupleOdometer.value_lt_power_length words.flatten
    have hbnd := boundary_stored base a b B C h0 h1 hi.1 _
      (BinaryArgmin.pick_fits hi.1.fits (hfit _ hrank)) hb
    have hscratch : b.stacks 779 = [] := by simpa [hb, stored] using hi.2.1
    have hcounterLength : (b.stacks 778).length = 2 * C + 3 := by
      simpa [hb, stored] using hi.2.2
    refine ⟨⟨hbnd, hscratch, hcounterLength⟩, hscratch, ?_⟩
    exact (body_space mass base a B C L K attemptCost entry hcore hfit words hw hi.1
      (hbound a hi) hB hC (hattempt words a hw hi.1 hc hi.2.1)
      (fun n d hd => hspace words a n d hw hi.1 hc hi.2.1 hd) he).bound
  have hnext : ∀ words a, words.map List.length = [C] →
      a.stacks counter.counter = Encoding.encodeList id words → I a →
      I (ExecCNFTupleEnumeration.advanceResult counter a words) := by
    intro words a hw _ hi
    refine ⟨boundary_stable base B C 0 a _
      (ExecCNFTupleEnumeration.advanceResult_outside counter a words) hi.1,
      ExecCNFTupleEnumeration.advanceResult_scratch counter a words, ?_⟩
    change ((ExecCNFTupleEnumeration.advanceResult counter a words).stacks
      counter.counter).length = _
    rw [ExecCNFTupleEnumeration.advanceResult_counter]
    simpa using Enumerators.encoded_shape_length
      ((ExecCNFTupleOdometer.bumpWords_lengths words).trans hw)
  have hp := Enumerators.visits_stack_bound counter (body mass) [C] I I L
    (max K (896 * L + 100 * (B + C + 1) + 1)) hbound hbound hcallback hnext
    hvis ⟨ha, hs, hc⟩
  intro k c hk ht i
  have h := hp k c hk ht i
  simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    Nat.add_zero] at h
  omega

/-- The complete scan, its initialization and final halt have the same storage
cap. Determinism transfers the proof to any execution of this fixed command. -/
theorem scan_halt_space (mass : Cmd 40 896) (base : State 40 896)
    (B C L K attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hB : B ≤ L) (hC : C ≤ L) (hcounterBound : 2 * C + 3 ≤ L)
    (hcounter : base.stacks 778 = Encoding.encodeList id [List.replicate C false])
    (hscratch : base.stacks 779 = []) (hseed : readEntry 770 771 base = entry 0)
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (hattempt : ∀ words a, words.map List.length = [C] → Boundary base B C a →
      a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n a b ∧
        b.stacks = Function.update (Function.update a.stacks 768
          (entry (CounterPrograms.value words.flatten)).payload) 769
          (entry (CounterPrograms.value words.flatten)).score)
    (hspace : ∀ words a n b, words.map List.length = [C] → Boundary base B C a →
      a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
      Eval (attempt mass) n a b → StageSpace (attempt mass) n a K)
    {steps : ℕ} {b : State 40 896}
    (he : Eval (ExecCNFTupleEnumeration.enumerate counter (body mass)) steps base b) :
    StageSpace (ExecCNFTupleEnumeration.enumerate counter (body mass)) (steps + 1) base
      (max K (896 * L + 100 * (B + C + 1) + 7 * (2 * C + 3) + 20)) := by
  have hi : Boundary base B C base := by
    refine ⟨fun _ _ _ _ _ => rfl, ?_⟩
    rw [hseed]
    exact hfit 0 (pow_pos (by decide) _)
  have spec := body_spec mass base B C attemptCost entry h0 h1 hcore hfit hattempt
  obtain ⟨n, d, hd, hvis, _, _, _, _⟩ :=
    ExecCNFTupleEnumeration.enumerate_correct counter (body mass) [C] (Boundary base B C)
      (attemptCost + (100 * (B + C + 1) + 1)) (boundary_stable base B C) spec
      [List.replicate C false] base (by simp) hi hcounter hscratch
      (by simp)
  have hsteps : steps = 1 + n := StreamResources.eval_steps_eq 778 777 he hd
  have hstart : Boundary base B C (ExecCNFTupleEnumeration.startResult counter base) :=
    boundary_stable base B C 0 base _ (fun _ _ _ => rfl) hi
  have hlength : ((ExecCNFTupleEnumeration.startResult counter base).stacks 778).length =
      2 * C + 3 := by
    simp [hcounter, Encoding.encodeList, Encoding.length_frame]
  have hloop := visits_space mass base B C L K attemptCost entry h0 h1 hcore hbase
    hB hC hcounterBound hfit hattempt hspace hvis hstart hscratch hlength
  constructor
  rw [hsteps]
  exact Enumerators.enumerate_stack_bound counter (body mass) hvis hloop

/-- The scan bound can be used directly as a stage inside the actual round. -/
theorem stage_space_of_halt_space {mass : Cmd 40 896} {steps bound : ℕ}
    {a : State 40 896}
    (h : StageSpace (ExecCNFTupleEnumeration.enumerate counter (body mass))
      (steps + 1) a bound) :
    StageSpace (ExecCNFTupleEnumeration.enumerate counter (body mass)) steps a bound := by
  constructor
  intro k c hk ht i
  exact h.bound k c (by omega) ht i

private theorem stage_mono {command : Cmd 40 896} {steps x y : ℕ}
    {a : State 40 896} (h : StageSpace command steps a x) (hxy : x ≤ y) :
    StageSpace command steps a y := by
  constructor
  intro k c hk ht i
  exact (h.bound k c hk ht i).trans hxy

private theorem local_stage {command : Cmd 40 896} {steps budget L : ℕ}
    {a : State 40 896} (hsteps : steps ≤ budget)
    (hL : ∀ i, (a.stacks i).length ≤ L) :
    StageSpace command steps a (896 * L + budget) := by
  constructor
  intro k c hk ht i
  exact StructuredSpace.local_stack_bound (compiled command 778 777)
    (StreamResources.dataBits_le_mul _ hL) k c (hk.trans hsteps) ht i

private theorem stored_bound (a b : State 40 896) (B C L : ℕ)
    (hL : ∀ i, (a.stacks i).length ≤ L) (hB : B ≤ L) (hC : C ≤ L)
    (winner : BinaryArgmin.Entry) (hw : BinaryArgmin.Fits B C winner)
    (hb : b.stacks = stored a winner) : ∀ i, (b.stacks i).length ≤ L := by
  intro i
  by_cases h768 : i = 768
  · subst i
    simp [hb, stored]
  by_cases h769 : i = 769
  · subst i
    simp [hb, stored]
  by_cases h770 : i = 770
  · subst i
    simpa [hb, stored] using hw.2.trans hC
  by_cases h771 : i = 771
  · subst i
    simpa [hb, stored] using hw.1.le.trans hB
  simpa [hb, stored, h768, h769, h770, h771] using hL i

/-- The actual complete round uses the same fixed polynomial storage cap:
one seed attempt, native install, the uniform scan, native append, and the
charged guard reset. The entry cap includes all previously retained history. -/
theorem round_halt_space (mass : Cmd 40 896) (a : State 40 896)
    (B C L K attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (h0 : a.stacks 768 = []) (h1 : a.stacks 769 = []) (hcore : CoreClean a)
    (hbp : a.stacks 770 = []) (hbs : a.stacks 771 = [])
    (hL : ∀ i, (a.stacks i).length ≤ L)
    (hB : B ≤ L) (hC : C ≤ L) (hcounterBound : 2 * C + 3 ≤ L)
    (hcounter : a.stacks 778 = Encoding.encodeList id [List.replicate C false])
    (hscratch : a.stacks 779 = [])
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (hattempt : ∀ words d, words.map List.length = [C] →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i) →
      d.stacks 778 = Encoding.encodeList id words → d.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n d b ∧
        b.stacks = Function.update (Function.update d.stacks 768
          (entry (CounterPrograms.value words.flatten)).payload) 769
          (entry (CounterPrograms.value words.flatten)).score)
    (hspace : ∀ words d n b, words.map List.length = [C] →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i) →
      d.stacks 778 = Encoding.encodeList id words → d.stacks 779 = [] →
      (∀ i, (d.stacks i).length ≤ L) →
      Eval (attempt mass) n d b → StageSpace (attempt mass) n d K)
    {steps : ℕ} {b : State 40 896} (he : Eval (round mass) steps a b) :
    StageSpace (round mass) (steps + 1) a
      (max K (896 * L + 100 * (B + C + 1) + 7 * (2 * C + 3) + 20)) := by
  let bound := max K (896 * L + 100 * (B + C + 1) + 7 * (2 * C + 3) + 20)
  have hzero := hfit 0 (pow_pos (by decide) C)
  obtain ⟨na, _, first, hea, hfirst⟩ := hattempt [List.replicate C false] a
    (by simp) (fun _ _ _ _ _ => rfl) hcounter hscratch
  have hfirst' : first.stacks = Function.update (Function.update a.stacks 768
      (entry 0).payload) 769 (entry 0).score := by
    simpa [CounterPrograms.value] using hfirst
  have hfirstCore : CoreClean first := by
    constructor <;> simp [hfirst', hcore.scratch772, hcore.scratch773,
      hcore.scratch774, hcore.scratch775, hcore.queue776]
  have hfirstBound : ∀ i, (first.stacks i).length ≤ L := by
    intro i
    by_cases h768 : i = 768
    · subst i
      simpa [hfirst'] using hzero.2.trans hC
    by_cases h769 : i = 769
    · subst i
      simpa [hfirst'] using hzero.1.le.trans hB
    simpa [hfirst', h768, h769] using hL i
  have hentry : readEntry 768 769 first = entry 0 := by simp [readEntry, hfirst']
  obtain ⟨ni, hni, seed, hei, hseed⟩ := NativeRound.install_eval first B C hfirstCore
    (by simp [hfirst', hbp]) (by simp [hfirst', hbs])
    (by simpa only [hentry] using hzero)
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
  obtain ⟨hseedCore, hs0, hs1, hseedEntry⟩ := stored_clean first (entry 0) hfirstCore seed hseed'
  have hseedBound := stored_bound first seed B C L hfirstBound hB hC (entry 0) hzero hseed'
  have hsCounter : seed.stacks 778 = Encoding.encodeList id [List.replicate C false] := by
    simp [hseed', stored, hfirst', hcounter]
  have hsScratch : seed.stacks 779 = [] := by simp [hseed', stored, hfirst', hscratch]
  have seedAttempt := fun words d hw (hd : Boundary seed B C d) hc hs =>
    hattempt words d hw
      (fun i h770 h771 h778 h779 => (hd.frame i h770 h771 h778 h779).trans
        (hframe i h770 h771 h778 h779)) hc hs
  obtain ⟨ns, _, final, hes, hfinal, hfScratch, hfCounter, _, _, _⟩ :=
    scan_minimum mass seed B C attemptCost entry hs0 hs1 hseedCore hsCounter hsScratch
      hseedEntry hfit seedAttempt
  have hscan := scan_halt_space mass seed B C L K attemptCost entry hs0 hs1 hseedCore
    hseedBound hB hC hcounterBound hsCounter hsScratch hseedEntry hfit seedAttempt
    (fun words d n b hw hd hc hs ht => hspace words d n b hw
      (fun i h770 h771 h778 h779 => (hd.frame i h770 h771 h778 h779).trans
        (hframe i h770 h771 h778 h779)) hc hs
      (boundary_stack_bound seed d B C L hseedBound hB hC hcounterBound hd hs (by
        have hlen : words.flatten.length = C := by
          have hh := congrArg List.sum hw
          simpa [List.length_flatten] using hh
        rw [hc, HashCandidateRank.tuple_eq_singleton_flatten hw]
        simp [Encoding.encodeList, Encoding.length_frame, hlen])) ht) hes
  have hfinalBound := boundary_stack_bound seed final B C L hseedBound hB hC hcounterBound
    hfinal hfScratch (by simp [hfCounter, Encoding.encodeList, Encoding.length_frame])
  obtain ⟨after, hep, _⟩ := NativeRound.append_eval final
  have happendCost : 5 * (final.stacks 770).length + 2 * (final.stacks 771).length + 11 ≤
      5 * C + 2 * B + 11 := by
    have hscore := hfinal.fits.1
    have hpayload := hfinal.fits.2
    dsimp only [readEntry] at hscore hpayload
    omega
  have hseedSpace : StageSpace (attempt mass) na a bound :=
    stage_mono (hspace [List.replicate C false] a na first (by simp)
      (fun _ _ _ _ _ => rfl) hcounter hscratch hL hea) (Nat.le_max_left _ _)
  have hinstallSpace : StageSpace install ni first bound := by
    apply stage_mono (local_stage hni hfirstBound)
    dsimp [bound]
    omega
  have happendSpace : StageSpace append
      (5 * (final.stacks 770).length + 2 * (final.stacks 771).length + 11) final bound := by
    apply stage_mono (local_stage happendCost hfinalBound)
    dsimp [bound]
    omega
  have hfull := round_halt_space_of_stages mass a first seed final after na ni ns
    (5 * (final.stacks 770).length + 2 * (final.stacks 771).length + 11) bound
    hea hei hes hep hseedSpace hinstallSpace (stage_space_of_halt_space hscan) happendSpace
  have hsteps := StreamResources.eval_steps_eq 778 777 he
    (round_eval_of_stages mass a first seed final after na ni ns
      (5 * (final.stacks 770).length + 2 * (final.stacks 771).length + 11) hea hei hes hep)
  rw [hsteps]
  exact hfull

private theorem row_boundary_core (base a : State 40 896) (rows : List (List Bool))
    (hc : CoreClean base) (ha : RowBoundary base rows a) : CoreClean a := by
  constructor
  · rw [ha.frame 772 (by decide) (by decide)]
    exact hc.scratch772
  · rw [ha.frame 773 (by decide) (by decide)]
    exact hc.scratch773
  · rw [ha.frame 774 (by decide) (by decide)]
    exact hc.scratch774
  · rw [ha.frame 775 (by decide) (by decide)]
    exact hc.scratch775
  · rw [ha.frame 776 (by decide) (by decide)]
    exact hc.queue776

private theorem read_credit (a : State 40 896) :
    ((HashSelectProgram.readCounterState outer a).stacks 781).length +
      (if (HashSelectProgram.readCounterState outer a).regs 9 then 1 else 0) =
        (a.stacks 781).length := by
  cases hw : a.stacks 781 <;>
    simp [HashSelectProgram.readCounterState, outer, readRegs, hw]

/-- All outer rounds retain only the attained history and a shrinking unary
counter. The history byte allowance is explicit and polynomial in the original
round count and row width; exponentially many losing rows are never retained. -/
theorem rounds_halt_space (mass : Cmd 40 896) (base : State 40 896)
    (B C L K attemptCost count : ℕ) (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (initial : List (List Bool)) (hhistory : base.stacks 777 = encodedHistory initial)
    (hdepth : (base.stacks 781).length = count)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hbp : base.stacks 770 = []) (hbs : base.stacks 771 = [])
    (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hB : B ≤ L) (hC : C ≤ L) (hcounterBound : 2 * C + 3 ≤ L)
    (hhistoryBound : (encodedHistory initial).length + count * (2 * C + 2) ≤ L)
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
          (entry rows (CounterPrograms.value words.flatten)).score)
    (hspace : ∀ rows a, rows.length ≤ initial.length + count → RowBoundary base rows a →
      (∃ q ≤ count, rows = HashSelectProgram.iter (nextRows entry C) q initial) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length + count * (2 * C + 2) →
      ∀ words d n b, words.map List.length = [C] →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i) →
      d.stacks 778 = Encoding.encodeList id words → d.stacks 779 = [] →
      (∀ i, (d.stacks i).length ≤ L) →
      Eval (attempt mass) n d b → StageSpace (attempt mass) n d K)
    {steps : ℕ} {b : State 40 896} (he : Eval (NativeRound.rounds mass) steps base b) :
    StageSpace (NativeRound.rounds mass) (steps + 1) base
      (max K (896 * L + 100 * (B + C + 1) + 7 * (2 * C + 3) + 20)) := by
  let bound := max K (896 * L + 100 * (B + C + 1) + 7 * (2 * C + 3) + 20)
  let rows := fun q => HashSelectProgram.iter (nextRows entry C) q initial
  let I := fun a : State 40 896 => ∃ q, q ≤ count ∧ RowBoundary base (rows q) a ∧
    q + (a.stacks 781).length + (if a.regs 9 then 1 else 0) = count
  have hcount : count ≤ L := by simpa only [hdepth] using hbase 781
  have hLb : L ≤ bound := by dsimp [bound]; omega
  have hrowBound : ∀ q a, q ≤ count → RowBoundary base (rows q) a →
      (a.stacks 781).length ≤ count → ∀ i, (a.stacks i).length ≤ L := by
    intro q a hq ha hcounterLength i
    by_cases h777 : i = 777
    · subst i
      rw [ha.history]
      have hh := encodedHistory_iter_length_le entry B C count initial hfit q hq
      have hm := Nat.mul_le_mul_right (2 * C + 2) hq
      exact hh.trans (by omega)
    by_cases h781 : i = 781
    · subst i
      exact hcounterLength.trans hcount
    rw [ha.frame i h777 h781]
    exact hbase i
  have hIbound : ∀ a, I a → ∀ i, (a.stacks i).length ≤ bound := by
    intro a hi i
    obtain ⟨q, hq, ha, hcredit⟩ := hi
    have hc : (a.stacks 781).length ≤ count := by omega
    exact (hrowBound q a hq ha hc i).trans hLb
  let iteration := Cmd.seq (round mass) (HashSelectProgram.readCounter outer)
  have hiteration : ∀ n a b, Eval iteration n a b → I a → a.regs 9 = true →
      I b ∧ StageSpace iteration n a bound := by
    intro n a b hab hi hflag
    obtain ⟨q, hq, ha, hcredit⟩ := hi
    have hcredit' : q + (a.stacks 781).length + 1 = count := by
      simpa only [hflag, ite_true] using hcredit
    have hq' : q < count := by omega
    have hlen : (rows q).length ≤ initial.length + count := by
      dsimp only [rows]
      rw [iter_length]
      omega
    have hreachable : ∃ j ≤ count, rows q = HashSelectProgram.iter (nextRows entry C) j initial :=
      ⟨q, hq, rfl⟩
    have hbytes : (encodedHistory (rows q)).length ≤
        (encodedHistory initial).length + count * (2 * C + 2) := by
      have hh := encodedHistory_iter_length_le entry B C count initial hfit q hq
      have hm := Nat.mul_le_mul_right (2 * C + 2) hq
      exact hh.trans (by omega)
    have haBound := hrowBound q a hq ha (by omega)
    have haCore := row_boundary_core base a (rows q) hcore ha
    have ha0 := (ha.frame 768 (by decide) (by decide)).trans h0
    have ha1 := (ha.frame 769 (by decide) (by decide)).trans h1
    have habp := (ha.frame 770 (by decide) (by decide)).trans hbp
    have habs := (ha.frame 771 (by decide) (by decide)).trans hbs
    have hacounter := (ha.frame 778 (by decide) (by decide)).trans hcounter
    have hascratch := (ha.frame 779 (by decide) (by decide)).trans hscratch
    dsimp only [iteration] at hab
    cases hab with
    | @seq _ _ nr nd a middle b hr hd =>
      obtain ⟨nt, _, last, winner, ht, hout, _, _, _, _, hbest⟩ :=
        round_minimum mass a B C attemptCost (entry (rows q)) ha0 ha1 haCore habp habs
          hacounter hascratch (hfit _ hlen) (hattempt _ a hlen ha hreachable hbytes)
      have hmid : middle.stacks = Function.update a.stacks 777
          (true :: (Encoding.frame (chosenEntry entry C (rows q)).payload.reverse ++
            a.stacks 777)) := by
        rw [hr.final_unique 778 ht, hout,
          hbest.trans (chosenEntry_eq_best entry C (rows q)).symm]
      have hmidRows : RowBoundary base (rows (q + 1)) middle := by
        have hh := rowBoundary_round base a middle (rows q) entry C ha hmid
        simpa only [rows, HashSelectProgram.iter_succ_apply] using hh
      have hmidCounter : middle.stacks 781 = a.stacks 781 := by simp [hmid]
      have hmidBound := hrowBound (q + 1) middle (by omega) hmidRows
        (by rw [hmidCounter]; omega)
      have hmidSpace := round_halt_space mass a B C L K attemptCost (entry (rows q))
        ha0 ha1 haCore habp habs haBound hB hC hcounterBound hacounter hascratch
        (hfit _ hlen) (hattempt _ a hlen ha hreachable hbytes) (hspace _ a hlen ha hreachable hbytes) hr
      have hroundSpace : StageSpace (round mass) nr a bound := by
        constructor
        intro k c hk hc i
        exact hmidSpace.bound k c (by omega) hc i
      have hb : b = HashSelectProgram.readCounterState outer middle :=
        hd.final_unique 778 (HashSelectProgram.readCounter_eval outer middle)
      have hnd : nd = 1 := StreamResources.eval_steps_eq 778 777 hd
        (HashSelectProgram.readCounter_eval outer middle)
      refine ⟨?_, ?_⟩
      · refine ⟨q + 1, by omega, ?_, ?_⟩
        · rw [hb]
          exact rowBoundary_read base middle (rows (q + 1)) hmidRows
        · rw [hb, Nat.add_assoc, read_credit, hmidCounter]
          omega
      · subst nd
        exact StageSpace.seq hr hd hroundSpace
          (readCounter_space middle bound (fun i => (hmidBound i).trans hLb))
  have hfull := he
  change Eval (.seq (HashSelectProgram.readCounter outer) (.while 9 iteration)) steps base b at he
  cases he with
  | @seq _ _ nr nl base middle b hr hl =>
    have hmiddle : middle = HashSelectProgram.readCounterState outer base :=
      hr.final_unique 778 (HashSelectProgram.readCounter_eval outer base)
    have hnr : nr = 1 := StreamResources.eval_steps_eq 778 777 hr
      (HashSelectProgram.readCounter_eval outer base)
    subst nr
    have hi : I middle := by
      refine ⟨0, Nat.zero_le _, ?_, ?_⟩
      · rw [hmiddle]
        apply rowBoundary_read base base initial
        exact ⟨fun _ _ _ => rfl, hhistory⟩
      · rw [hmiddle, Nat.zero_add, read_credit, hdepth]
    have hloop := StructuredSpace.loop_stack_bound iteration 9 778 777 I bound hIbound
      (fun n a b h hi hf => (hiteration n a b h hi hf).1)
      (fun n a b h hi hf => (hiteration n a b h hi hf).2.bound) hl hi
    have hwhole := StageSpace.seq hr hl
      (readCounter_space base bound (fun i => (hbase i).trans hLb)) ⟨hloop⟩
    exact ⟨StructuredSpace.compiled_halt_stack_bound hfull 778 777 hwhole.bound⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace
