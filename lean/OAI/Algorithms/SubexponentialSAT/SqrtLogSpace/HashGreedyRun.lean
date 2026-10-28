import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution

/-! Concrete CNF scores instantiate the actual unary-controlled greedy run.
The only execution seam is the actual per-mark query. Initial-code distance
is used only for the final zero-mass and exact model-set consequences. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun

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

/-- The complete native rounds retain exactly the deterministic CNF history.
No separate candidate evaluator or aggregate mass oracle is assumed. -/
theorem rounds_eval {n m depth : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
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
      Ready (fun words => words = workspace (trialState d m depth word)) a →
      ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
        workspace middle = workspace (trialState d m depth word) ∧
        read middle = read a ∧
        BinaryArithmetic.toNat (middle.stacks 323) = markedCount
          (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth word.reverse :: rows)
          (fun e x => !(clauses e).eval x) e ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t
          (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
          (state recordPorts middle false true false tail [])) :
    ∃ t ≤ HashSelectProgram.roundsBudget
      (roundBudget (attemptBudget base n m depth queryCost)
        (HashSelect.loopCap n m) (HashCandidates.payloadWidth m depth)) (HashSelect.loopCap n m),
      ∃ b, Eval (NativeRound.rounds (mass query)) t base b ∧
        RowBoundary base (HashGreedyCNF.history clauses depth initial (HashSelect.loopCap n m)) b ∧
        b.stacks 781 = [] ∧ b.regs 9 = false := by
  apply rounds_history (mass query) base (HashSelect.loopCap n m)
    (HashCandidates.payloadWidth m depth) (attemptBudget base n m depth queryCost)
    (HashSelect.loopCap n m) (HashGreedyCNF.entry clauses depth) initial
    hhistory hdepth h0 h1 hcore hbp hbs hcounter hs
  · intro rows _ rank _
    exact HashGreedyCandidate.entry_fits _ _ n m depth rows rank
  intro rows a hrows ha hactual hbytes words d hwords hd hcounterD hsD
  have hword : words.flatten.length = HashCandidates.payloadWidth m depth := by
    have hh := congrArg List.sum hwords
    simpa [List.length_flatten] using hh
  have hsingle : words = [words.flatten] := HashCandidateRank.tuple_eq_singleton_flatten hwords
  have hf : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i := by
    intro i h770 h771 h777 h778 h779 h781
    exact (hd i h770 h771 h778 h779).trans (ha.frame i h777 h781)
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
  have hcounterD' : d.stacks 778 = Encoding.encodeList id [words.flatten] := by
    exact hcounterD.trans (congrArg (Encoding.encodeList id) hsingle)
  have hhistD : d.stacks 777 = encodedHistory rows :=
    (hd 777 (by decide) (by decide) (by decide) (by decide)).trans ha.history
  obtain ⟨t, ht, b, he, hb⟩ := attempt_eval clauses hm rows query queryCost d words.flatten
    hword hcounterD'
    (loader_clean d
      ((hf 768 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0)
      ((hf 769 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1)
      hcoreD hsD) hlowD
    (by rw [hf 767 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht)
    (by rw [hf 780 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwidth)
    (by rw [hf 780 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hvalue)
    (by rw [hf 782 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hmword)
    (by rw [hf 818 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hshape)
    hcD (hq rows words.flatten d hrows hactual hbytes hword hf hhistD hcounterD' hsD)
  refine ⟨t, ?_, b, he, hb⟩
  have hbudget : attemptBudget d n m depth queryCost = attemptBudget base n m depth queryCost := by
    simp only [attemptBudget, massBudget, LeafOuterProgram.routeCost,
      hf 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hf 769 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hf 782 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact hbudget ▸ ht

/-- Concrete per-boundary staged attempt, with a uniform cost over the actual
history-byte domain. Its frame reconstruction is shared by time and space proofs. -/
theorem staged_boundary_attempt {n m depth : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (query : Cmd 40 896) (queryCost : List Bool → ℕ)
    (base : State 40 896)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hlow : ∀ i : Fin 896, i.val < 12 → base.stacks i = [])
    (ht : base.stacks 767 = [])
    (hwidth : (base.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (base.stacks 780) = 3 * m)
    (hmword : CounterPrograms.value (base.stacks 782) = m)
    (hshape : (base.stacks 818).length = HashSelect.loopCap n m)
    (hcollector : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → base.stacks i = [])
    (L : ℕ)
    (hsource : ∀ i ∈ ([782,783,784,785] : List (Fin 896)), (base.stacks i).length ≤ L)
    (hC : HashCandidates.payloadWidth m depth ≤ L)
    (hempty : ∀ i ∈ HashMassStaged.stagedPorts, base.stacks i = [])
    (rows : List (List Bool)) (a : State 40 896) (ha : RowBoundary base rows a)
    (hbytes : (encodedHistory rows).length ≤ L)
    (words : List (List Bool)) (d : State 40 896)
    (hwords : words.map List.length = [HashCandidates.payloadWidth m depth])
    (hd : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i)
    (hcounterD : d.stacks 778 = Encoding.encodeList id words) (hsD : d.stacks 779 = [])
    (hq : ∀ (e : Fin m) tail (a : State 40 896),
      Ready (fun ws => ws = workspace
        (LeafOuterNative.trialStaged (trialState d m depth words.flatten))) a →
      ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
        workspace middle = workspace (LeafOuterNative.trialStaged (trialState d m depth words.flatten)) ∧
        read middle = read a ∧
        BinaryArithmetic.toNat (middle.stacks 323) = markedCount
          (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth words.flatten.reverse :: rows)
          (fun e x => !(clauses e).eval x) e ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t
          (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
          (state recordPorts middle false true false tail [])) :
    ∃ t ≤ stagedAttemptBudget base n m depth queryCost L, ∃ b,
      Eval (attempt (HashMassStaged.command query)) t d b ∧
      b.stacks = Function.update (Function.update d.stacks 768
        (HashGreedyCNF.entry clauses depth rows (CounterPrograms.value words.flatten)).payload) 769
        (HashGreedyCNF.entry clauses depth rows (CounterPrograms.value words.flatten)).score := by
  have hword : words.flatten.length = HashCandidates.payloadWidth m depth := by
    have hh := congrArg List.sum hwords
    simpa [List.length_flatten] using hh
  have hsingle : words = [words.flatten] := HashCandidateRank.tuple_eq_singleton_flatten hwords
  have hf : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i := by
    intro i h770 h771 h777 h778 h779 h781
    exact (hd i h770 h771 h778 h779).trans (ha.frame i h777 h781)
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
  have hcounterD' : d.stacks 778 = Encoding.encodeList id [words.flatten] := by
    exact hcounterD.trans (congrArg (Encoding.encodeList id) hsingle)
  have hhistD : d.stacks 777 = encodedHistory rows :=
    (hd 777 (by decide) (by decide) (by decide) (by decide)).trans ha.history
  obtain ⟨t, ht, b, he, hb⟩ := staged_attempt_eval clauses hm rows query queryCost d words.flatten
    hword hcounterD'
    (loader_clean d
      ((hf 768 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0)
      ((hf 769 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1)
      hcoreD hsD) hlowD
    (by rw [hf 767 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht)
    (by rw [hf 780 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwidth)
    (by rw [hf 780 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hvalue)
    (by rw [hf 782 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hmword)
    (by rw [hf 818 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hshape)
    hcD L
    (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl
      · rw [hhistD]
        exact hbytes
      · rw [hf 782 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hsource 782 (by simp)
      · rw [hf 783 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hsource 783 (by simp)
      · rw [hf 784 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hsource 784 (by simp)
      · rw [hf 785 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hsource 785 (by simp)) hC
    (by
      intro i hi
      have hsmall : i.val < 770 := by
        simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil,
          or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      have hneq (j : Fin 896) (hj : 770 ≤ j.val) : i ≠ j := by
        intro he
        subst i
        omega
      rw [hf i (hneq 770 (by decide)) (hneq 771 (by decide)) (hneq 777 (by decide))
        (hneq 778 (by decide)) (hneq 779 (by decide)) (hneq 781 (by decide))]
      exact hempty i hi) hq
  refine ⟨t, ?_, b, he, hb⟩
  have hbudget : stagedAttemptBudget d n m depth queryCost L = stagedAttemptBudget base n m depth queryCost L := by
    simp only [stagedAttemptBudget, attemptBudget, massBudget, LeafOuterProgram.routeCost,
      hf 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hf 769 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hf 782 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact hbudget ▸ ht

theorem staged_rounds_eval {n m depth : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
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
    (L : ℕ)
    (hsource : ∀ i ∈ ([782,783,784,785] : List (Fin 896)), (base.stacks i).length ≤ L)
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
          (state recordPorts middle false true false tail [])) :
    ∃ t ≤ HashSelectProgram.roundsBudget
      (roundBudget (stagedAttemptBudget base n m depth queryCost L)
        (HashSelect.loopCap n m) (HashCandidates.payloadWidth m depth)) (HashSelect.loopCap n m),
      ∃ b, Eval (NativeRound.rounds (HashMassStaged.command query)) t base b ∧
        RowBoundary base (HashGreedyCNF.history clauses depth initial (HashSelect.loopCap n m)) b ∧
        b.stacks 781 = [] ∧ b.regs 9 = false := by
  apply rounds_history (HashMassStaged.command query) base (HashSelect.loopCap n m)
    (HashCandidates.payloadWidth m depth) (stagedAttemptBudget base n m depth queryCost L)
    (HashSelect.loopCap n m) (HashGreedyCNF.entry clauses depth) initial
    hhistory hdepth h0 h1 hcore hbp hbs hcounter hs
  · intro rows _ rank _
    exact HashGreedyCandidate.entry_fits _ _ n m depth rows rank
  intro rows a hrows ha hactual hbytes words d hwords hd hcounterD hsD
  apply staged_boundary_attempt clauses hm query queryCost base h0 h1 hcore hlow ht
    hwidth hvalue hmword hshape hcollector L hsource hC hempty rows a ha
    (hbytes.trans hbytesL) words d hwords hd hcounterD hsD
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
    (hcounterD.trans (congrArg (Encoding.encodeList id) hsingle)) hsD

open scoped BigOperators

/-- The literal history returned by the native run accepts exactly the ambient
models. Its unmarked count is the exact CNF count, and positivity is SAT. This
is a semantic readback, not a claim that the final unmarked query has run. -/
theorem exit_exact_models {n m depth : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (initial : List (List Bool)) (base b : State 40 896)
    (hcode : ∀ v : HashSelect.Row m,
      (∀ r ∈ initial.map (HashGreedyCNF.decode m), (∑ e, r e * v e) = 0) → v ≠ 0 →
        m ≤ depth * SparseCode.weight v)
    (hout : RowBoundary base
      (HashGreedyCNF.history clauses depth initial (HashSelect.loopCap n m)) b) :
    ∃ rows : List (List Bool), b.stacks 777 = encodedHistory rows ∧
      HashSelect.mass (HashGreedyCNF.rowAccept clauses) (HashInput.violationWeight clauses) rows = 0 ∧
      HashSelect.acceptedCount (HashGreedyCNF.rowAccept clauses) rows =
        SAT.count (Finset.univ.image clauses) ∧
      (0 < HashSelect.acceptedCount (HashGreedyCNF.rowAccept clauses) rows ↔
        SAT.Satisfiable (Finset.univ.image clauses)) := by
  let rows := HashGreedyCNF.history clauses depth initial (HashSelect.loopCap n m)
  have hc : HashSelect.acceptedCount (HashGreedyCNF.rowAccept clauses) rows =
      SAT.count (Finset.univ.image clauses) := by
    rw [HashGreedyCNF.history_count_eq clauses hm depth initial hcode]
    unfold SAT.count SAT.satisfyingAssignments
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro x _
    have hcnf : SAT.CNF.eval x (Finset.univ.image clauses) = true ↔
        ∀ i, (clauses i).eval x = true := by simp
    simp only [hcnf]
  refine ⟨rows, hout.history, HashGreedyCNF.history_mass_zero clauses hm depth initial hcode,
    hc, ?_⟩
  rw [hc, SAT.count_pos_iff]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun
