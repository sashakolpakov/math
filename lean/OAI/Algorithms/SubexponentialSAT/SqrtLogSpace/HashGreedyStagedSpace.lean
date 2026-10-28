import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStagedSpace

/-! Prefix storage for the physically staged candidate attempt. The full marked-query
runtime never appears in this bound: the marked queries supply an independent
prefix cap, while preparation, reference setup and padding are polynomial. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashMassAdapter HashGreedyExecution

/-- One fixed allowance for all source prefixes of a concrete candidate attempt. -/
def attemptSpace (a : State 40 896) (n m depth L K : ℕ) : ℕ :=
  max K (896 * (3 * L + 2) + HashCandidateProgram.Leaf.budget m depth +
    (LeafOuterProgram.routeCost (782,0) a + LeafOuterNative.References.budget (a.stacks 782) + 1) +
      50 * (3 * L + 3) + 59 * L + 23 * HashSelect.loopCap n m + 150)

theorem attemptSpace_congr (a b : State 40 896) (n m depth L K : ℕ)
    (h0 : a.stacks 0 = b.stacks 0) (h782 : a.stacks 782 = b.stacks 782) :
    attemptSpace a n m depth L K = attemptSpace b n m depth L K := by
  simp only [attemptSpace, LeafOuterProgram.routeCost, h0, h782]

theorem attempt_halt_space {n m depth : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (rows : List (List Bool)) (query : Cmd 40 896)
    (queryCost : List Bool → ℕ) (a : State 40 896) (word : List Bool) (L K : ℕ)
    (hL : ∀ i, (a.stacks i).length ≤ L)
    (hpayload : HashCandidates.payloadWidth m depth ≤ L) (hscore : HashSelect.loopCap n m ≤ L)
    (href : (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2)
    (hgrowth : outputGrowth (fun _ => n + 1) (RowSelectionProgram.Index.alphabet m) ≤ 3 * L + 2)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hcounter : a.stacks 778 = Encoding.encodeList id [word])
    (hclean : ∀ j : Fin 11, j ≠ 2 → j ≠ 3 → j ≠ 9 →
      a.stacks (HashCandidateProgram.Leaf.loaderStacks j) = [])
    (hlow : ∀ j : Fin 896, j.val < 12 → a.stacks j = []) (ht : a.stacks 767 = [])
    (hwidth : (a.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (a.stacks 780) = 3 * m)
    (hmword : CounterPrograms.value (a.stacks 782) = m)
    (hshape : (a.stacks 818).length = HashSelect.loopCap n m)
    (hcollector : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → a.stacks i = [])
    (hempty : ∀ i ∈ HashMassStaged.stagedPorts, a.stacks i = [])
    (hq : ∀ (e : Fin m) tail (base : State 40 896),
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged (trialState a m depth word))) base →
      ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
        workspace middle = workspace (LeafOuterNative.trialStaged (trialState a m depth word)) ∧ read middle = read base ∧
        BinaryArithmetic.toNat (middle.stacks 323) = markedCount
          (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth word.reverse :: rows)
          (fun e x => !(clauses e).eval x) e ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t (state recordPorts base false true false tail (Encoding.encodeNat e.val).reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ (e : Fin m) tail base t middle,
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged (trialState a m depth word))) base →
      (read base).length ≤ 3 * L + 2 → tail.length ≤ 3 * L + 2 →
      (Encoding.encodeNat e.val).length ≤ 3 * L + 2 → n + 1 ≤ 3 * L + 2 →
      Eval query t (state recordPorts base false true false tail (Encoding.encodeNat e.val).reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query t (state recordPorts base false true false tail (Encoding.encodeNat e.val).reverse) K)
    {steps : ℕ} {result : State 40 896} (he : Eval (attempt (HashMassStaged.command query)) steps a result) :
    StageSpace (attempt (HashMassStaged.command query)) (steps + 1) a (attemptSpace a n m depth L K) := by
  let trialRows := HashCandidates.normalize m depth word.reverse :: rows
  obtain ⟨np, hnp, b, hp, hprep⟩ := HashCandidateProgram.Leaf.prepare_eval hm a word
    hword hcounter hclean hlow ht hwidth hvalue
  have hws : workspace (LeafOuterNative.trialStaged b) =
      workspace (LeafOuterNative.trialStaged (trialState a m depth word)) := by
    have hs := HashMassStaged.staged_stacks_congr b (trialState a m depth word) hprep
    exact congrArg (fun words => fun i => words (workPort i)) hs
  have hbempty : ∀ i ∈ HashMassStaged.stagedPorts, b.stacks i = [] := by
    intro i hi
    have hne : i ≠ 768 := by
      simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [hprep, hne, hempty i hi]
  have hb : ReferencesReady b := by
    constructor
    · simp [hprep, ht]
    · intro i hi
      have hempty : a.stacks i = [] := by
        rcases hi with hi | rfl
        · exact hlow i (by omega)
        · exact hcollector 320 (by decide) (by decide)
      have hne : i ≠ 768 := by
        intro hi768
        subst i
        rcases hi with hi | hi
        · exact (by decide : ¬ (768 : Fin 896).val < 9) hi
        · exact (by decide : (768 : Fin 896) ≠ 320) hi
      simp [hprep, hne, hempty]
  have hbL : ∀ i, (b.stacks i).length ≤ L := by
    intro i
    by_cases hi : i = 768
    · subst i
      simpa [hprep] using hpayload
    · simpa [hprep, hi] using hL i
  have hq' : ∀ bits tail (base : State 40 896),
      (∃ e : Fin m, bits = Encoding.encodeNat e.val) →
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged b)) base →
      ∃ t middle, t ≤ queryCost bits ∧ workspace middle = workspace (LeafOuterNative.trialStaged b) ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) =
          referenceCount clauses trialRows bits ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []) := by
    intro bits tail base hvalid hready
    obtain ⟨e, rfl⟩ := hvalid
    simpa only [hws, referenceCount_encode, trialRows] using
      hq e tail base (by simpa only [hws] using hready)
  have hspace' : ∀ bits tail base t middle, (∃ e : Fin m, bits = Encoding.encodeNat e.val) →
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged b)) base →
      (read base).length ≤ 3 * L + 2 → tail.length ≤ 3 * L + 2 →
      bits.length ≤ 3 * L + 2 → n + 1 ≤ 3 * L + 2 →
      Eval query t (state recordPorts base false true false tail bits.reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query t (state recordPorts base false true false tail bits.reverse) K := by
    intro bits tail base t middle hvalid hready hr ht' hbits hw hrun
    obtain ⟨e, rfl⟩ := hvalid
    exact hspace e tail base t middle (by simpa only [hws] using hready) hr ht' hbits hw hrun
  have hbcollector : ∀ i : Fin 896, 321 ≤ i.val → i.val ≤ 324 → b.stacks i = [] := by
    intro i hi hj
    have hne : i ≠ 768 := by intro h; subst i; omega
    simp [hprep, hne, hcollector i (by omega) hj]
  obtain ⟨nq, _, c, hmass, hquery⟩ := HashMassStaged.eval query (referenceCount clauses trialRows)
    queryCost (fun _ => n + 1) (fun bits => ∃ e : Fin m, bits = Encoding.encodeNat e.val) b m hb
    (by simpa [hprep] using hmword) hbcollector hbempty (fun e => ⟨e, rfl⟩) hq'
  have hmassSpace := HashMassStagedSpace.command_halt_space query (referenceCount clauses trialRows)
    queryCost (fun _ => n + 1) (fun bits => ∃ e : Fin m, bits = Encoding.encodeNat e.val) b m L K hb
    (by simpa [hprep] using hmword) hbL hbcollector
    (fun e => ⟨e, rfl⟩) href hgrowth hq' hspace' hmass
  rw [reference_sum] at hquery
  have hlen : (DisjointReuse.binaryNat (HashSelect.mass (HashGreedyCNF.rowAccept clauses)
      (HashInput.violationWeight clauses) trialRows)).length ≤ HashSelect.loopCap n m :=
    HashGreedyCandidate.canonical_mass_length _ _ n m trialRows (by simp [SAT.Assignment])
      (fun x => by simpa using HashInput.violationWeight_le clauses x)
  have hcL : ∀ i, (c.stacks i).length ≤ L := by
    intro i
    by_cases hi : i = 769
    · subst i
      simpa [hquery] using hlen.trans hscore
    · simpa [hquery, hi] using hbL i
  have hcshape : (c.stacks 818).length = HashSelect.loopCap n m := by simp [hquery, hprep, hshape]
  obtain ⟨last, hpad, _⟩ := PadScore.leaf_eval c
    (by simp [hquery, hprep, hlow 0 (by decide)])
    (by simp [hquery, hprep, hlow 1 (by decide)])
    (by simp [hquery, hprep, hlow 2 (by decide)]) (by simpa [hquery, hprep, hshape] using hlen)
  have hprepSpace : StageSpace HashCandidateProgram.Leaf.prepare np a (attemptSpace a n m depth L K) := by
    constructor
    intro k state hk htrace i
    have h := StructuredSpace.local_stack_bound (compiled HashCandidateProgram.Leaf.prepare 778 777)
      (StreamResources.dataBits_le_mul _ hL) k state (hk.trans hnp) htrace i
    unfold attemptSpace
    omega
  have hmassBound : StageSpace (HashMassStaged.command query) nq b (attemptSpace a n m depth L K) := by
    constructor
    intro k state hk htrace i
    have h := hmassSpace.bound k state (by omega) htrace i
    have hroute : LeafOuterProgram.routeCost (782,0) b = LeafOuterProgram.routeCost (782,0) a := by
      simp [LeafOuterProgram.routeCost, hprep]
    have hword782 : b.stacks 782 = a.stacks 782 := by simp [hprep]
    unfold HashMassStagedSpace.spaceBudget at h
    rw [hroute, hword782] at h
    unfold attemptSpace
    omega
  have hpadSpace : StageSpace PadScore.leafCommand (23 * (c.stacks 818).length + 20) c
      (attemptSpace a n m depth L K) := by
    constructor
    intro k state hk htrace i
    have h := StructuredSpace.local_stack_bound (compiled PadScore.leafCommand 778 777)
      (StreamResources.dataBits_le_mul _ hcL) k state hk htrace i
    rw [hcshape] at h
    unfold attemptSpace
    omega
  have hfull := hp.seq (hmass.seq hpad)
  have hstage := StageSpace.seq hp (hmass.seq hpad) hprepSpace
    (StageSpace.seq hmass hpad hmassBound hpadSpace)
  have hsteps := StreamResources.eval_steps_eq 778 777 he hfull
  rw [hsteps]
  exact ⟨StructuredSpace.compiled_halt_stack_bound hfull 778 777 hstage.bound⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace
