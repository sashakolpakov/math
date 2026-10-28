import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter

/-! All-prefix storage for the actual marked-record collector. The parser and
native addition have polynomial local work. Expensive marked queries supply
their own actual prefix bound; their total runtime is never used as workspace. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashMassAdapter HashGreedyProgram.NativeRound

private theorem workPort_covers (i : Fin 896) (hi : i.val < 320 ∨ 324 < i.val) :
    ∃ j : Fin 891, workPort j = i := by
  rcases hi with hi | hi
  · refine ⟨⟨i.val, by omega⟩, ?_⟩
    apply Fin.ext
    simp [workPort, hi]
  · refine ⟨⟨i.val - 5, by omega⟩, ?_⟩
    apply Fin.ext
    have h : ¬i.val - 5 < 320 := by omega
    simp [workPort, h]
    omega

/-- All 896 words are charged, including the caller workspace and the unread
record tail. This also applies immediately after a query before its addition. -/
theorem state_stack_bound (ready : (Fin 891 → List Bool) → Prop) (L : ℕ)
    (hready : ∀ frame, ready frame → ∀ i, (frame i).length ≤ L)
    (base : HashMassAdapter.Data) (v pr f : Bool) (src payload : List Bool)
    (hb : ready (workspace base)) (hacc : (read base).length ≤ L)
    (hresult : (base.stacks 323).length ≤ L) (hscratch : (base.stacks 324).length ≤ L)
    (hsource : src.length ≤ L) (hpayload : payload.length ≤ L) :
    ∀ i, ((state recordPorts base v pr f src payload).stacks i).length ≤ L := by
  intro i
  by_cases h320 : i = 320
  · subst i
    simpa [state, recordPorts] using hsource
  by_cases h321 : i = 321
  · subst i
    simpa [state, recordPorts] using hpayload
  by_cases h322 : i = 322
  · subst i
    simpa [state, recordPorts, HashMassAdapter.read] using hacc
  by_cases h323 : i = 323
  · subst i
    simpa [state, recordPorts] using hresult
  by_cases h324 : i = 324
  · subst i
    simpa [state, recordPorts] using hscratch
  have hi : i.val < 320 ∨ 324 < i.val := by
    have : i.val ≠ 320 := fun h => h320 (Fin.ext h)
    have : i.val ≠ 321 := fun h => h321 (Fin.ext h)
    have : i.val ≠ 322 := fun h => h322 (Fin.ext h)
    have : i.val ≠ 323 := fun h => h323 (Fin.ext h)
    have : i.val ≠ 324 := fun h => h324 (Fin.ext h)
    omega
  obtain ⟨j, hj⟩ := workPort_covers i hi
  have h := hready (workspace base) hb j
  simpa [state, recordPorts, h320, h321, workspace, hj] using h

private theorem ready_state_bound (ready : (Fin 891 → List Bool) → Prop) (L : ℕ)
    (hready : ∀ frame, ready frame → ∀ i, (frame i).length ≤ L)
    (base : HashMassAdapter.Data) (v pr f : Bool) (src payload : List Bool)
    (hb : Ready ready base) (hacc : (read base).length ≤ L)
    (hsource : src.length ≤ L) (hpayload : payload.length ≤ L) :
    ∀ i, ((state recordPorts base v pr f src payload).stacks i).length ≤ L :=
  state_stack_bound ready L hready base v pr f src payload hb.workspace_ready hacc
    (by simp [hb.result_empty]) (by simp [hb.scratch_empty]) hsource hpayload

private theorem afterTag_bound (ready : (Fin 891 → List Bool) → Prop) (L : ℕ)
    (hready : ∀ frame, ready frame → ∀ i, (frame i).length ≤ L)
    (base : HashMassAdapter.Data) (records : List (List Bool)) (suffix : List Bool)
    (hb : Ready ready base) (hacc : (read base).length ≤ L)
    (hsource : (Encoding.encodeList id records ++ suffix).length ≤ L) :
    ∀ i, ((afterTag recordPorts base records suffix).stacks i).length ≤ L := by
  cases records with
  | nil =>
    apply ready_state_bound ready L hready base false true false suffix [] hb hacc
    · have h : 1 + suffix.length ≤ L := by simpa using hsource
      omega
    · simp
  | cons bits rest =>
    apply ready_state_bound ready L hready base true true false _ [] hb hacc
    · simp only [Encoding.encodeList, List.length_cons, List.length_append, id_eq] at hsource ⊢
      omega
    · simp

private theorem local_space {command : Code} {n budget L K : ℕ}
    {a : HashMassAdapter.Data} (hn : n ≤ budget) (hbudget : budget ≤ 20 * (L + 1) + 10)
    (hL : ∀ i, (a.stacks i).length ≤ L) :
    StageSpace command n a (max K (896 * L + 20 * (L + 1) + 10)) := by
  constructor
  intro k c hk ht i
  have h := StructuredSpace.local_stack_bound (compiled command 778 777)
    (StreamResources.dataBits_le_mul _ hL) k c (hk.trans hn) ht i
  have hm := Nat.le_max_right K (896 * L + 20 * (L + 1) + 10)
  omega

/-- Actual record-loop executions have a common prefix cap. The accumulator
allowance is its initial word length plus the sum of per-record width growth. -/
theorem loop_space (query : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 891 → List Bool) → Prop) (valid : List Bool → Prop) (L K : ℕ)
    (hready : ∀ frame, ready frame → ∀ i, (frame i).length ≤ L)
    (hq : ∀ bits tail (base : HashMassAdapter.Data), valid bits → Ready ready base →
      ∃ n middle, n ≤ queryCost bits ∧ ready (workspace middle) ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
        (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
        Eval query n (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ bits tail base n middle, valid bits → Ready ready base →
      (read base).length ≤ L → tail.length ≤ L → bits.length ≤ L → width bits ≤ L →
      Eval query n (state recordPorts base false true false tail bits.reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query n (state recordPorts base false true false tail bits.reverse) K)
    (records : List (List Bool)) (suffix : List Bool) (base : HashMassAdapter.Data)
    (hrecords : ∀ bits ∈ records, valid bits) (hb : Ready ready base)
    (hacc : (read base).length + outputGrowth width records ≤ L)
    (hsource : (Encoding.encodeList id records ++ suffix).length ≤ L) :
    ∃ n next, Ready ready next ∧
      (read next).length ≤ (read base).length + outputGrowth width records ∧
      Eval (RecordPrograms.loop recordPorts (callback query)) n
        (afterTag recordPorts base records suffix) (state recordPorts next false true false suffix []) ∧
      StageSpace (RecordPrograms.loop recordPorts (callback query)) n
        (afterTag recordPorts base records suffix) (max K (896 * L + 20 * (L + 1) + 10)) := by
  let bound := max K (896 * L + 20 * (L + 1) + 10)
  have hLb : L ≤ bound := by dsimp [bound]; omega
  induction records generalizing base with
  | nil =>
    have he : Eval (RecordPrograms.loop recordPorts (callback query)) 1
        (afterTag recordPorts base [] suffix) (state recordPorts base false true false suffix []) :=
      Eval.while_false (by simp [afterTag])
    refine ⟨1, base, hb, by simp [outputGrowth], he, ?_⟩
    have hstart := afterTag_bound ready L hready base [] suffix hb (by simpa [outputGrowth] using hacc)
      hsource
    exact ⟨StructuredSpace.while_false_stack_bound _ _ _ (by simp [afterTag])
      (fun i => (hstart i).trans hLb) _ _ _ (compiled_site _ 778 777)⟩
  | cons bits rest ih =>
    let tail := Encoding.encodeList id rest ++ suffix
    have hv := hrecords bits (by simp)
    have hgrowth : (read base).length + (width bits + 1) + outputGrowth width rest ≤ L := by
      simpa [outputGrowth, Nat.add_assoc] using hacc
    have haccL : (read base).length ≤ L := by omega
    have hwidth : width bits ≤ L := by omega
    have hsource' : 2 * bits.length + (Encoding.encodeList id rest).length + 2 + suffix.length ≤ L := by
      simpa [List.length_append, Encoding.length_encodeList_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsource
    have htail : tail.length ≤ L := by simp only [tail, List.length_append]; omega
    have hbits : bits.length ≤ L := by omega
    obtain ⟨n, middle, _, hm, hr, _, hw, hs, hquery⟩ := hq bits tail base hv hb
    obtain ⟨na, next, hna, hnext, hread, hadd⟩ :=
      add_count_eval ready middle tail (read base) (middle.stacks 323) hm hr rfl hs
    have hlength : (read next).length ≤ (read base).length + width bits + 1 := by
      rw [hread]
      have hh := BinaryArithmetic.length_add (read base) (middle.stacks 323)
      omega
    have hnextAcc : (read next).length + outputGrowth width rest ≤ L := by omega
    obtain ⟨nt, final, hfinal, hfinalLength, hrest, hrestSpace⟩ :=
      ih next (fun b h => hrecords b (by simp [h])) hnext hnextAcc htail
    have hquerySpace : StageSpace query n
        (state recordPorts base false true false tail bits.reverse) bound := by
      constructor
      intro k c hk ht i
      exact ((hspace bits tail base n middle hv hb haccL htail hbits hwidth hquery).bound
        k c hk ht i).trans (Nat.le_max_left _ _)
    have hmiddleBound := state_stack_bound ready L hready middle false true false tail [] hm
      (by rw [hr]; exact haccL) (hw.trans hwidth) (by simp [hs]) htail (by simp)
    have haddSpace : StageSpace (Mass.invoke massPorts) na
        (state recordPorts middle false true false tail []) bound :=
      local_space hna (by omega) hmiddleBound
    have hcallback := hquery.seq hadd
    have hcallbackSpace := StageSpace.seq hquery hadd hquerySpace haddSpace
    have hreader : Eval (reader recordPorts) (6 * bits.length + 4)
        (afterTag recordPorts base (bits :: rest) suffix)
        (state recordPorts base false true false tail bits.reverse) := by
      simpa [afterTag, tail] using reader_eval recordPorts base bits tail [] true true false
    have hreaderSpace : StageSpace (reader recordPorts) (6 * bits.length + 4)
        (afterTag recordPorts base (bits :: rest) suffix) bound :=
      local_space le_rfl (by omega)
        (afterTag_bound ready L hready base (bits :: rest) suffix hb haccL hsource)
    have hpop : Eval
        (.ite recordPorts.found (atom (.set recordPorts.tag false))
          (atom (.pop recordPorts.source recordPorts.tag recordPorts.present))) 2
        (state recordPorts next false true false tail []) (afterTag recordPorts next rest suffix) := by
      apply Eval.ite_false (by simp)
      exact pop_list_eval recordPorts next rest suffix false true
    have hpopSpace : StageSpace
        (.ite recordPorts.found (atom (.set recordPorts.tag false))
          (atom (.pop recordPorts.source recordPorts.tag recordPorts.present)))
        2 (state recordPorts next false true false tail []) bound :=
      local_space le_rfl (by omega)
        (ready_state_bound ready L hready next false true false tail [] hnext
          (by omega) htail (by simp))
    have hbody := hreader.seq (hcallback.seq hpop)
    have hbodySpace := StageSpace.seq hreader (hcallback.seq hpop) hreaderSpace
      (StageSpace.seq hcallback hpop hcallbackSpace hpopSpace)
    refine ⟨(6 * bits.length + 4 + (n + na + 2)) + nt + 1, final, hfinal, ?_,
      Eval.while_true (by simp [afterTag]) hbody hrest, ?_⟩
    · simp only [outputGrowth, List.map_cons, List.sum_cons] at hfinalLength ⊢
      omega
    · exact ⟨StructuredSpace.while_true_stack_bound (by simp [afterTag]) hbody hrest 778 777
        hbodySpace.bound hrestSpace.bound _ _ _ (compiled_site _ 778 777)⟩

/-- Initial parser setup and the actual final halt preserve the uniform cap.
This exposes a source stage for composition into the concrete mass attempt. -/
theorem command_space (query : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 891 → List Bool) → Prop) (valid : List Bool → Prop) (L K : ℕ)
    (hready : ∀ frame, ready frame → ∀ i, (frame i).length ≤ L)
    (hq : ∀ bits tail (base : HashMassAdapter.Data), valid bits → Ready ready base →
      ∃ n middle, n ≤ queryCost bits ∧ ready (workspace middle) ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
        (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
        Eval query n (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ bits tail base n middle, valid bits → Ready ready base →
      (read base).length ≤ L → tail.length ≤ L → bits.length ≤ L → width bits ≤ L →
      Eval query n (state recordPorts base false true false tail bits.reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query n (state recordPorts base false true false tail bits.reverse) K)
    (records : List (List Bool)) (suffix : List Bool) (base : HashMassAdapter.Data)
    (hrecords : ∀ bits ∈ records, valid bits) (hb : Ready ready base)
    (hacc : (read base).length + outputGrowth width records ≤ L)
    (hsource : (Encoding.encodeList id records ++ suffix).length ≤ L) (v pr f : Bool) :
    ∃ n next, Ready ready next ∧
      (read next).length ≤ (read base).length + outputGrowth width records ∧
      Eval (HashMassAdapter.command query) n
        (state recordPorts base v pr f (Encoding.encodeList id records ++ suffix) [])
        (state recordPorts next false true false suffix []) ∧
      StageSpace (HashMassAdapter.command query) (n + 1)
        (state recordPorts base v pr f (Encoding.encodeList id records ++ suffix) [])
        (max K (896 * L + 20 * (L + 1) + 10)) := by
  obtain ⟨n, next, hn, hlength, hloop, hloopSpace⟩ :=
    loop_space query count queryCost width ready valid L K hready hq hspace
      records suffix base hrecords hb hacc hsource
  have haccL : (read base).length ≤ L := by omega
  have hset := set_found_eval recordPorts base v pr f false
    (Encoding.encodeList id records ++ suffix) []
  have hpop := pop_list_eval recordPorts base records suffix v pr
  have hsetSpace : StageSpace (atom (.set recordPorts.found false)) 1
      (state recordPorts base v pr f (Encoding.encodeList id records ++ suffix) [])
      (max K (896 * L + 20 * (L + 1) + 10)) :=
    local_space le_rfl (by omega)
      (ready_state_bound ready L hready base v pr f _ [] hb haccL hsource (by simp))
  have hpopSpace : StageSpace
      (atom (.pop recordPorts.source recordPorts.tag recordPorts.present)) 1
      (state recordPorts base v pr false (Encoding.encodeList id records ++ suffix) [])
      (max K (896 * L + 20 * (L + 1) + 10)) :=
    local_space le_rfl (by omega)
      (ready_state_bound ready L hready base v pr false _ [] hb haccL hsource (by simp))
  have he := hset.seq (hpop.seq hloop)
  have hstage := StageSpace.seq hset (hpop.seq hloop) hsetSpace
    (StageSpace.seq hpop hloop hpopSpace hloopSpace)
  exact ⟨1 + (1 + n), next, hn, hlength, he,
    ⟨StructuredSpace.compiled_halt_stack_bound he 778 777 hstage.bound⟩⟩

/-- The actual compiled collector call inherits every prefix of its callee,
including the callee halt that is relocated to the caller's return jump. -/
theorem collector_space (query : Code) (count queryCost width : List Bool → ℕ)
    (valid : List Bool → Prop) (a : HashMassAdapter.Data) (records : List (List Bool))
    (L K : ℕ) (hL : ∀ i, (a.stacks i).length ≤ L)
    (hsource : a.stacks 320 = Encoding.encodeList id records)
    (h321 : a.stacks 321 = []) (h322 : a.stacks 322 = [])
    (h323 : a.stacks 323 = []) (h324 : a.stacks 324 = [])
    (hrecords : ∀ bits ∈ records, valid bits) (hgrowth : outputGrowth width records ≤ L)
    (hq : ∀ bits tail (base : HashMassAdapter.Data), valid bits →
      Ready (fun words => words = workspace a) base →
      ∃ n middle, n ≤ queryCost bits ∧ workspace middle = workspace a ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
        (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
        Eval query n (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ bits tail base n middle, valid bits →
      Ready (fun words => words = workspace a) base →
      (read base).length ≤ L → tail.length ≤ L → bits.length ≤ L → width bits ≤ L →
      Eval query n (state recordPorts base false true false tail bits.reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query n (state recordPorts base false true false tail bits.reverse) K)
    {steps : ℕ} {b : HashMassAdapter.Data}
    (he : Eval (.call (HashMassAdapter.program query)) steps a b) :
    StageSpace (.call (HashMassAdapter.program query)) steps a
      (max K (896 * L + 20 * (L + 1) + 10)) := by
  have hready : ∀ frame, frame = workspace a → ∀ i, (frame i).length ≤ L := by
    intro frame hf i
    rw [hf]
    exact hL (workPort i)
  obtain ⟨n, next, _, _, ht, hstage⟩ := command_space query count queryCost width
    (fun words => words = workspace a) valid L K hready hq hspace records [] a hrecords
    ⟨rfl, h323, h324⟩ (by simpa [HashMassAdapter.read, h322] using hgrowth)
    (by simpa [← hsource] using hL 320) (a.regs 16) (a.regs 17) (a.regs 18)
  have hstart : state recordPorts a (a.regs 16) (a.regs 17) (a.regs 18)
      (Encoding.encodeList id records ++ []) [] = a := by
    apply state_eq_self recordPorts a _ _ _ _ _ rfl rfl rfl
    · simpa only [recordPorts, List.append_nil] using hsource
    · exact h321
  rw [hstart] at ht hstage
  have htrace := compiled_halt_trace ht 320 322
  have hcall : Eval (.call (HashMassAdapter.program query)) (n + 1) a
      (state recordPorts next false true false [] []) := Eval.call _ htrace
  have hsteps := StreamResources.eval_steps_eq 778 777 he hcall
  rw [hsteps]
  exact ⟨StructuredSpace.call_stack_bound (HashMassAdapter.program query)
    (compiled (.call (HashMassAdapter.program query)) 778 777)
    (siteAddress (.call (HashMassAdapter.program query)))
    (exitAddress (.call (HashMassAdapter.program query)))
    (compiled_site (.call (HashMassAdapter.program query)) 778 777) htrace hstage.bound⟩

/-- Reference generation, every marked query and addition, and final canonical
handoff all obey one bound. Only polynomial setup and finish costs occur in the
space expression; the expensive query contributes its independent prefix cap. -/
theorem mass_halt_space (query : Code) (count queryCost width : List Bool → ℕ)
    (valid : List Bool → Prop) (a : HashMassAdapter.Data) (m L K : ℕ)
    (ha : ReferencesReady a) (hm : CounterPrograms.value (a.stacks 782) = m)
    (hL : ∀ i, (a.stacks i).length ≤ L)
    (h321 : a.stacks 321 = []) (h322 : a.stacks 322 = [])
    (h323 : a.stacks 323 = []) (h324 : a.stacks 324 = [])
    (hvalid : ∀ e : Fin m, valid (Encoding.encodeNat e.val))
    (hrefLength : (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ L)
    (hgrowth : outputGrowth width (RowSelectionProgram.Index.alphabet m) ≤ L)
    (hq : ∀ bits tail (base : HashMassAdapter.Data), valid bits →
      Ready (fun words => words = workspace a) base →
      ∃ n middle, n ≤ queryCost bits ∧ workspace middle = workspace a ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
        (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
        Eval query n (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ bits tail base n middle, valid bits →
      Ready (fun words => words = workspace a) base →
      (read base).length ≤ L → tail.length ≤ L → bits.length ≤ L → width bits ≤ L →
      Eval query n (state recordPorts base false true false tail bits.reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query n (state recordPorts base false true false tail bits.reverse) K)
    {steps : ℕ} {b : HashMassAdapter.Data} (he : Eval (mass query) steps a b) :
    StageSpace (mass query) (steps + 1) a
      (max K (896 * L +
        (LeafOuterProgram.routeCost (782,0) a + LeafOuterNative.References.budget (a.stacks 782) + 1) +
        50 * (L + 1) + 30)) := by
  let bound := max K (896 * L +
    (LeafOuterProgram.routeCost (782,0) a + LeafOuterNative.References.budget (a.stacks 782) + 1) +
    50 * (L + 1) + 30)
  obtain ⟨np, prepared, hnp, hp, hprepared⟩ := references_eval a ha
  have hws : workspace prepared = workspace a := by
    funext i
    have hi : workPort i ≠ 320 := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [workPort] at hv
      split_ifs at hv <;> simp only at hv <;> omega
    simp [workspace, hprepared, hi]
  have hpreparedSource : prepared.stacks 320 =
      Encoding.encodeList id (RowSelectionProgram.Index.alphabet m) := by
    simp [hprepared, hm, ProgramEncoding.encodeRecords]
  have hpreparedBound : ∀ i, (prepared.stacks i).length ≤ L := by
    intro i
    by_cases hi : i = 320
    · subst i
      simpa only [hpreparedSource] using hrefLength
    simpa [hprepared, hi] using hL i
  have hrecords : ∀ bits ∈ RowSelectionProgram.Index.alphabet m, valid bits := by
    intro bits hb
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    exact hvalid ⟨j, by simpa using hj⟩
  obtain ⟨nc, _, collected, hc, _, hlen, hframe⟩ :=
    collector_eval query count queryCost width valid prepared (RowSelectionProgram.Index.alphabet m)
      hpreparedSource (by simp [hprepared, h321]) (by simp [hprepared, h322])
      (by simp [hprepared, h323]) (by simp [hprepared, h324]) hrecords
      (by simpa only [hws] using hq)
  have hcollector := collector_space query count queryCost width valid prepared
    (RowSelectionProgram.Index.alphabet m) L K hpreparedBound hpreparedSource
    (by simp [hprepared, h321]) (by simp [hprepared, h322])
    (by simp [hprepared, h323]) (by simp [hprepared, h324]) hrecords hgrowth
    (by simpa only [hws] using hq) (by simpa only [hws] using hspace) hc
  have hcollectedBound : ∀ i, (collected.stacks i).length ≤ L := by
    intro i
    by_cases hi322 : i = 322
    · subst i
      exact hlen.trans hgrowth
    by_cases hi320 : i = 320
    · subst i
      rw [hframe]
      simp
    rw [hframe]
    simpa [hi320, hi322] using hpreparedBound i
  obtain ⟨nf, hnf, last, hf, _⟩ := finish_eval collected
    (by rw [hframe]; simp [hprepared, h323]) (by rw [hframe]; simp [hprepared, h324])
    (by rw [hframe]; simp [hprepared, ha.scratch]) L (hcollectedBound 322) (hcollectedBound 769)
  have hprepSpace : StageSpace references np a bound := by
    constructor
    intro k c hk ht i
    have hh := StructuredSpace.local_stack_bound (compiled references 778 777)
      (StreamResources.dataBits_le_mul _ hL) k c (hk.trans hnp) ht i
    dsimp only [bound]
    have hmax := Nat.le_max_right K (896 * L +
      (LeafOuterProgram.routeCost (782,0) a + LeafOuterNative.References.budget (a.stacks 782) + 1) +
      50 * (L + 1) + 30)
    omega
  have hcollectSpace : StageSpace (.call (HashMassAdapter.program query)) nc prepared bound := by
    constructor
    intro k c hk ht i
    have hh := hcollector.bound k c hk ht i
    dsimp [bound]
    omega
  have hfinishSpace : StageSpace finish nf collected bound := by
    constructor
    intro k c hk ht i
    have hh := StructuredSpace.local_stack_bound (compiled finish 778 777)
      (StreamResources.dataBits_le_mul _ hcollectedBound) k c (hk.trans hnf) ht i
    dsimp [bound]
    omega
  have hfull := hp.seq (hc.seq hf)
  have hstage := StageSpace.seq hp (hc.seq hf) hprepSpace
    (StageSpace.seq hc hf hcollectSpace hfinishSpace)
  have hsteps := StreamResources.eval_steps_eq 778 777 he hfull
  rw [hsteps]
  exact ⟨StructuredSpace.compiled_halt_stack_bound hfull 778 777 hstage.bound⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace
