import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace

/-! Uniform source-prefix storage for the actual physically staged greedy run.
The caller and attained-history bounds are maintained by the actual loops;
the expensive marked query contributes only its independent prefix cap. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRunSpace

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound
open HashMassAdapter HashGreedyExecution

private theorem loader_clean (a : State 40 896)
    (h0 : a.stacks 768 = []) (h1 : a.stacks 769 = []) (hcore : CoreClean a)
    (hs : a.stacks 779 = []) :
    ∀ j : Fin 11, j ≠ 2 → j ≠ 3 → j ≠ 9 →
      a.stacks (HashCandidateProgram.Leaf.loaderStacks j) = [] := by
  rcases hcore with ⟨h2,h3,h4,h5,h6⟩
  intro j hj2 hj3 hj9
  fin_cases j <;> simp_all [HashCandidateProgram.Leaf.loaderStacks]

theorem boundary_attempt_space {n m depth : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (query : Cmd 40 896) (queryCost : List Bool → ℕ)
    (base : State 40 896)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hlow : ∀ i : Fin 896, i.val < 12 → base.stacks i = []) (ht : base.stacks 767 = [])
    (hwidth : (base.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (base.stacks 780) = 3 * m)
    (hmword : CounterPrograms.value (base.stacks 782) = m)
    (hshape : (base.stacks 818).length = HashSelect.loopCap n m)
    (hcollector : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → base.stacks i = [])
    (hempty : ∀ i ∈ HashMassStaged.stagedPorts, base.stacks i = [])
    (L K : ℕ) (hC : HashCandidates.payloadWidth m depth ≤ L) (hB : HashSelect.loopCap n m ≤ L)
    (href : (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2)
    (hgrowth : outputGrowth (fun _ => n + 1) (RowSelectionProgram.Index.alphabet m) ≤ 3 * L + 2)
    (rows : List (List Bool)) (word : List Bool) (d : State 40 896)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hf : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i)
    (hcounterD : d.stacks 778 = Encoding.encodeList id [word]) (hsD : d.stacks 779 = [])
    (hdL : ∀ i, (d.stacks i).length ≤ L)
    (hq : ∀ (e : Fin m) tail (a : State 40 896),
      Ready (fun ws => ws = workspace
        (LeafOuterNative.trialStaged (trialState d m depth word))) a →
      ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
        workspace middle = workspace (LeafOuterNative.trialStaged (trialState d m depth word)) ∧
        read middle = read a ∧
        BinaryArithmetic.toNat (middle.stacks 323) = markedCount
          (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth word.reverse :: rows)
          (fun e x => !(clauses e).eval x) e ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t
          (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ (e : Fin m) tail a t middle,
      Ready (fun ws => ws = workspace (LeafOuterNative.trialStaged (trialState d m depth word))) a →
      (read a).length ≤ 3 * L + 2 → tail.length ≤ 3 * L + 2 →
      (Encoding.encodeNat e.val).length ≤ 3 * L + 2 → n + 1 ≤ 3 * L + 2 →
      Eval query t (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query t (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse) K)
    {steps : ℕ} {result : State 40 896}
    (he : Eval (attempt (HashMassStaged.command query)) steps d result) :
    StageSpace (attempt (HashMassStaged.command query)) (steps + 1) d
      (HashGreedyStagedSpace.attemptSpace base n m depth L K) := by
  have hcoreD : CoreClean d := by
    constructor
    · rw [hf 772 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch772
    · rw [hf 773 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch773
    · rw [hf 774 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch774
    · rw [hf 775 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch775
    · rw [hf 776 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcore.queue776
  have hlowD : ∀ i : Fin 896, i.val < 12 → d.stacks i = [] := by
    intro i hi
    have hneq (j : Fin 896) (hj : 12 ≤ j.val) : i ≠ j := by
      intro he
      subst i
      omega
    rw [hf i (hneq 770 (by decide)) (hneq 771 (by decide)) (hneq 777 (by decide))
      (hneq 778 (by decide)) (hneq 779 (by decide)) (hneq 781 (by decide))]
    exact hlow i hi
  have hcD : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → d.stacks i = [] := by
    intro i hi hj
    have hneq (j : Fin 896) (hj : 324 < j.val) : i ≠ j := by
      intro he
      subst i
      omega
    rw [hf i (hneq 770 (by decide)) (hneq 771 (by decide)) (hneq 777 (by decide))
      (hneq 778 (by decide)) (hneq 779 (by decide)) (hneq 781 (by decide))]
    exact hcollector i hi hj
  have hemptyD : ∀ i ∈ HashMassStaged.stagedPorts, d.stacks i = [] := by
    intro i hi
    have hsmall : i.val < 770 := by
      simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hneq (j : Fin 896) (hj : 770 ≤ j.val) : i ≠ j := by intro h; subst i; omega
    rw [hf i (hneq 770 (by decide)) (hneq 771 (by decide)) (hneq 777 (by decide))
      (hneq 778 (by decide)) (hneq 779 (by decide)) (hneq 781 (by decide))]
    exact hempty i hi
  have h := HashGreedyStagedSpace.attempt_halt_space clauses hm rows query queryCost d word L K
    hdL hC hB href hgrowth hword hcounterD
    (loader_clean d
      ((hf 768 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0)
      ((hf 769 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1)
      hcoreD hsD) hlowD
    (by rw [hf 767 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht)
    (by rw [hf 780 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwidth)
    (by rw [hf 780 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hvalue)
    (by rw [hf 782 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hmword)
    (by rw [hf 818 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hshape)
    hcD hemptyD hq hspace he
  rw [HashGreedyStagedSpace.attemptSpace_congr d base n m depth L K
    (hf 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf 782 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))] at h
  exact h

theorem rounds_halt_space {n m depth : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (initial : List (List Bool)) (query : Cmd 40 896)
    (queryCost : List Bool → ℕ) (base : State 40 896)
    (hhistory : base.stacks 777 = encodedHistory initial)
    (hdepth : (base.stacks 781).length = HashSelect.loopCap n m)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hbp : base.stacks 770 = []) (hbs : base.stacks 771 = [])
    (hcounter : base.stacks 778 = Encoding.encodeList id
      [List.replicate (HashCandidates.payloadWidth m depth) false])
    (hs : base.stacks 779 = [])
    (hlow : ∀ i : Fin 896, i.val < 12 → base.stacks i = [])
    (ht : base.stacks 767 = [])
    (hwidth : (base.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (base.stacks 780) = 3 * m)
    (hmword : CounterPrograms.value (base.stacks 782) = m)
    (hshape : (base.stacks 818).length = HashSelect.loopCap n m)
    (hcollector : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → base.stacks i = [])
    (L K : ℕ) (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hB : HashSelect.loopCap n m ≤ L)
    (hcounterBound : 2 * HashCandidates.payloadWidth m depth + 3 ≤ L)
    (href : (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2)
    (hgrowth : outputGrowth (fun _ => n + 1) (RowSelectionProgram.Index.alphabet m) ≤ 3 * L + 2)
    (hC : HashCandidates.payloadWidth m depth ≤ L)
    (hbytesL : (encodedHistory initial).length +
      HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) ≤ L)
    (hempty : ∀ i ∈ HashMassStaged.stagedPorts, base.stacks i = [])
    (hq : ∀ rows word (d : State 40 896),
      rows.length ≤ initial.length + HashSelect.loopCap n m →
      (∃ q ≤ HashSelect.loopCap n m, rows = HashGreedyCNF.history clauses depth initial q) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length +
        HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) →
      word.length = HashCandidates.payloadWidth m depth →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
        d.stacks i = base.stacks i) →
      d.stacks 777 = encodedHistory rows → d.stacks 778 = Encoding.encodeList id [word] →
      d.stacks 779 = [] → ∀ (e : Fin m) tail (a : State 40 896),
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged (trialState d m depth word))) a →
      ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
        workspace middle = workspace (LeafOuterNative.trialStaged (trialState d m depth word)) ∧
        read middle = read a ∧
        BinaryArithmetic.toNat (middle.stacks 323) = markedCount
          (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth word.reverse :: rows)
          (fun e x => !(clauses e).eval x) e ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t
          (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ rows word (d : State 40 896),
      rows.length ≤ initial.length + HashSelect.loopCap n m →
      (∃ q ≤ HashSelect.loopCap n m, rows = HashGreedyCNF.history clauses depth initial q) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length +
        HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) →
      word.length = HashCandidates.payloadWidth m depth →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
        d.stacks i = base.stacks i) →
      d.stacks 777 = encodedHistory rows → d.stacks 778 = Encoding.encodeList id [word] →
      d.stacks 779 = [] → (∀ i, (d.stacks i).length ≤ L) →
      ∀ (e : Fin m) tail a t middle,
      Ready (fun ws => ws = workspace (LeafOuterNative.trialStaged (trialState d m depth word))) a →
      (read a).length ≤ 3 * L + 2 → tail.length ≤ 3 * L + 2 →
      (Encoding.encodeNat e.val).length ≤ 3 * L + 2 → n + 1 ≤ 3 * L + 2 →
      Eval query t (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query t (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse) K)
    {steps : ℕ} {result : State 40 896}
    (he : Eval (NativeRound.rounds (HashMassStaged.command query)) steps base result) :
    StageSpace (NativeRound.rounds (HashMassStaged.command query)) (steps + 1) base
      (max (HashGreedyStagedSpace.attemptSpace base n m depth L K)
        (896 * L + 100 * (HashSelect.loopCap n m + HashCandidates.payloadWidth m depth + 1) +
          7 * (2 * HashCandidates.payloadWidth m depth + 3) + 20)) := by
  apply HashGreedyScanSpace.rounds_halt_space (HashMassStaged.command query) base
    (HashSelect.loopCap n m) (HashCandidates.payloadWidth m depth) L
    (HashGreedyStagedSpace.attemptSpace base n m depth L K)
    (stagedAttemptBudget base n m depth queryCost L) (HashSelect.loopCap n m)
    (HashGreedyCNF.entry clauses depth) initial hhistory hdepth h0 h1 hcore hbp hbs
    hbase hB hC hcounterBound hbytesL hcounter hs
    (fun rows _ rank _ => HashGreedyCandidate.entry_fits _ _ n m depth rows rank) ?_ ?_ he
  · intro rows a hrows ha hactual hbytes words d hwords hd hc hsD
    apply HashGreedyRun.staged_boundary_attempt clauses hm query queryCost base h0 h1 hcore hlow ht
      hwidth hvalue hmword hshape hcollector L (fun i _ => hbase i) hC hempty rows a ha
      (hbytes.trans hbytesL) words d hwords hd hc hsD
    have hword : words.flatten.length = HashCandidates.payloadWidth m depth := by
      have hh := congrArg List.sum hwords
      simpa [List.length_flatten] using hh
    have hsingle : words = [words.flatten] := HashCandidateRank.tuple_eq_singleton_flatten hwords
    have hf : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
        d.stacks i = base.stacks i := by
      intro i h770 h771 h777 h778 h779 h781
      exact (hd i h770 h771 h778 h779).trans (ha.frame i h777 h781)
    exact hq rows words.flatten d hrows hactual hbytes hword hf
      ((hd 777 (by decide) (by decide) (by decide) (by decide)).trans ha.history)
      (hc.trans (congrArg (Encoding.encodeList id) hsingle)) hsD
  · intro rows a hrows ha hactual hbytes words d t b hwords hd hc hsD hdL htD
    have hword : words.flatten.length = HashCandidates.payloadWidth m depth := by
      have hh := congrArg List.sum hwords
      simpa [List.length_flatten] using hh
    have hsingle : words = [words.flatten] := HashCandidateRank.tuple_eq_singleton_flatten hwords
    have hf : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
        d.stacks i = base.stacks i := by
      intro i h770 h771 h777 h778 h779 h781
      exact (hd i h770 h771 h778 h779).trans (ha.frame i h777 h781)
    have hhist : d.stacks 777 = encodedHistory rows :=
      (hd 777 (by decide) (by decide) (by decide) (by decide)).trans ha.history
    have hcounterD : d.stacks 778 = Encoding.encodeList id [words.flatten] :=
      hc.trans (congrArg (Encoding.encodeList id) hsingle)
    have hbound := boundary_attempt_space clauses hm query queryCost base h0 h1 hcore hlow ht
      hwidth hvalue hmword hshape hcollector hempty L K hC hB href hgrowth rows words.flatten d
      hword hf hcounterD hsD hdL
      (hq rows words.flatten d hrows hactual hbytes hword hf hhist hcounterD hsD)
      (hspace rows words.flatten d hrows hactual hbytes hword hf hhist hcounterD hsD hdL) htD
    constructor
    intro k c hk hc'
    exact hbound.bound k c (by omega) hc'

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRunSpace
