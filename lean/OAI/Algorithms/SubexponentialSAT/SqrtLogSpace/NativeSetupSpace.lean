import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeFrontend
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ScheduleProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram

/-! Concrete canonical startup through the disjoint sparsification parameters.
The only large-instance premises concern the numeric schedule. All parsing,
normalization, arithmetic, clearing, and caller storage belong to one run. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls BinaryArithmetic

def budgetStacks : Fin 32 ↪ Fin 1220 :=
  (Fin.castAddEmb 1188).trans
    ((Equiv.swap (0 : Fin 1220) 266).toEmbedding.trans
      ((Equiv.swap (1 : Fin 1220) 259).toEmbedding.trans
        (Equiv.swap (2 : Fin 1220) 264).toEmbedding))

theorem budgetStacks_val (i : Fin 32) :
    (budgetStacks i).val = if i = 0 then 266 else if i = 1 then 259
      else if i = 2 then 264 else i.val := by
  fin_cases i <;> rfl

@[simp] theorem budgetStacks_zero : budgetStacks 0 = 266 := by decide
@[simp] theorem budgetStacks_one : budgetStacks 1 = 259 := by decide
@[simp] theorem budgetStacks_two : budgetStacks 2 = 264 := by decide

def budgetCall (k : ℕ) : Cmd 80 1220 :=
  .call (ProgramLinking.liftProgram (DisjointReuse.SparseBudgetProgram.program k)
    (Fin.castAdd 72) budgetStacks)

def clearSchedule : Cmd 80 1220 := clearSequence [1, 2, 3, 4]

def setupAfterFrontend (k : ℕ) : Cmd 80 1220 :=
  .seq (.seq ScheduleProgram.readySharedCall clearSchedule) (budgetCall k)

def setupCommand (k : ℕ) : Cmd 80 1220 := .seq frontendCommand (setupAfterFrontend k)

def setupProgram (k : ℕ) := compiled (setupCommand k) ABI.countStack ABI.answerStack

theorem scheduleStacks_val (i : Fin 32) :
    (ScheduleProgram.sharedStacks i).val =
      if i = 0 then 267 else if i = 5 then 266 else i.val := by
  fin_cases i <;> rfl

theorem scheduleStacks_off (i : Fin 1220) (hi : 32 ≤ i.val)
    (h266 : i ≠ 266) (h267 : i ≠ 267) :
    ¬ ∃ j, ScheduleProgram.sharedStacks j = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  rw [scheduleStacks_val] at hv
  split_ifs at hv with h0 h5
  · exact h267 (Fin.ext hv.symm)
  · exact h266 (Fin.ext hv.symm)
  · have := j.isLt
    omega

theorem budgetStacks_off (i : Fin 1220) (hi : 32 ≤ i.val)
    (h266 : i ≠ 266) (h259 : i ≠ 259) (h264 : i ≠ 264) :
    ¬ ∃ j, budgetStacks j = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  rw [budgetStacks_val] at hv
  split_ifs at hv with h0 h1 h2
  · exact h266 (Fin.ext hv.symm)
  · exact h259 (Fin.ext hv.symm)
  · exact h264 (Fin.ext hv.symm)
  · have := j.isLt
    omega

theorem budgetCall_eval (k : ℕ) (hk : 2 ≤ k) (s : List Bool) (a : State 80 1220)
    (hports : ∀ j, a.stacks (budgetStacks j) = if j = 0 then s else []) :
    ∃ steps b M B,
      Eval (budgetCall k) steps a b ∧
      steps ≤ DisjointReuse.SparseBudgetProgram.commandCost k s + 1 ∧
      toNat M = DisjointReuse.SparseBudget.chooseM k 1 (toNat s) (by decide) ∧
      toNat B = 4 * toNat M ^ (k - 1) ∧
      (∀ j, b.stacks (budgetStacks j) = if j = 0 then s else if j = 1 then M
        else if j = 2 then B else []) ∧
      (∀ i, (¬ ∃ j, budgetStacks j = i) → b.stacks i = a.stacks i) := by
  let localData := projectState (Fin.castAdd 72) budgetStacks a
  obtain ⟨t, rf, M, B, he, hM, hB, ht⟩ :=
    DisjointReuse.SparseBudgetProgram.command_eval k hk localData.regs s
  have hstart : DisjointReuse.ParametersProgram.state localData.regs
      (DisjointReuse.SparseBudgetProgram.inputWords s) = localData := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      have hp := hports i
      change _ = a.stacks (budgetStacks i)
      rw [hp]
      fin_cases i <;> rfl
  have htrace := compiled_halt_trace he (DisjointReuse.ParametersProgram.port 0)
    (DisjointReuse.ParametersProgram.port 1)
  rw [hstart] at htrace
  let out := DisjointReuse.ParametersProgram.state rf
    (DisjointReuse.SparseBudgetProgram.outputWords s M B)
  refine ⟨t + 1, embedState (Fin.castAdd 72) budgetStacks a out, M, B,
    eval_call_from_state _ _ _ a (Fin.castAdd_injective 8 72)
      budgetStacks.injective htrace, by omega, hM, hB, ?_, ?_⟩
  · intro j
    rw [embedState_stack _ _ _ _ budgetStacks.injective]
    fin_cases j <;> rfl
  · intro i hi
    exact embedState_stack_frame _ _ _ _ i hi

theorem frontendReady_stack_bound {n : ℕ} (F : SAT.CNF (Fin n)) (binary : List Bool)
    (a : State 80 1220) (ha : FrontendReady F binary a) (hlen : binary.length ≤ n) :
    ∀ i, (a.stacks i).length ≤ Encoding.formulaBitLength F + 1 := by
  intro i
  have hn := Encoding.numVariables_le_formulaBitLength F
  by_cases hi : i = ABI.countStack
  · subst i
    rw [ha.input]
    exact Nat.le_succ _
  by_cases hu : i = 258
  · subst i
    rw [ha.header, Encoding.length_encodeNat]
    omega
  by_cases hb : i = 265
  · subst i
    rw [ha.body]
    have hl := SubexpNormalizationCorrectness.normalizedBody_length_le F
    have hh : (Encoding.encodeCNFBody F).length ≤ Encoding.formulaBitLength F := by
      rw [Encoding.formulaBitLength_eq]
      omega
    omega
  by_cases hd : i = 267
  · subst i
    rw [ha.dimension]
    omega
  rw [ha.blank i hi hu hb hd]
  simp

theorem schedule_clear_eval (n : ℕ) (binary : List Bool) (a : State 80 1220)
    (hv : toNat binary = n) (hn : 20 ≤ n) (W : ℕ)
    (hports : ∀ j : Fin 32, a.stacks (ScheduleProgram.sharedStacks j) =
      if j = 0 then binary else [])
    (hwidth : ∀ i, (a.stacks i).length ≤ W) :
    ∃ steps b s,
      Eval (.seq ScheduleProgram.readySharedCall clearSchedule) steps a b ∧
      toNat s = sparsifySchedule n ∧ s.length ≤ n ∧
      b.stacks = Function.update a.stacks 266 s ∧
      steps ≤ 9 * 10000002 * (n + binary.length + 6) ^ 3 + 9760 * W + 20 := by
  obtain ⟨t, rf, words, hs, h0, h5, hlen5, htime⟩ :=
    ScheduleProgram.readySharedCall_eval binary (by omega) a hports
  let mid := embedState (Fin.castAdd 72) ScheduleProgram.sharedStacks
    (ScheduleProgram.resetSharedState a) ⟨rf, ScheduleProgram.slots words⟩
  change Eval ScheduleProgram.readySharedCall t a mid at hs
  have hlocal : ∀ j, mid.stacks (ScheduleProgram.sharedStacks j) =
      ScheduleProgram.slots words j :=
    fun j => embedState_stack _ _ _ _ ScheduleProgram.sharedStacks.injective j
  have hframe : ∀ i, (¬ ∃ j, ScheduleProgram.sharedStacks j = i) →
      mid.stacks i = a.stacks i := by
    intro i hi
    exact embedState_stack_frame _ _ _ _ i hi
  let D := 1220 * W + t + 1
  have htotal : stackBits mid.stacks ≤ D := by
    have hgrowth := trace_dataBits _
      (compiled_halt_trace hs ABI.countStack ABI.answerStack)
    have hstart := StreamResources.dataBits_le_mul
      (a.withPC (some (compiled ScheduleProgram.readySharedCall
        ABI.countStack ABI.answerStack).entry)) hwidth
    change stackBits mid.stacks ≤ stackBits a.stacks + (t + 1) at hgrowth
    change stackBits a.stacks ≤ 1220 * W at hstart
    dsimp [D]
    omega
  have hmid : ∀ i, (mid.stacks i).length ≤ D := by
    intro i
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le ((mid.stacks j).length))
      (Finset.mem_univ i)).trans htotal
  obtain ⟨u, b, hu, he, hclear, hkeep, _⟩ := clearSequence_eval [1, 2, 3, 4] mid D hmid
  refine ⟨t + u, b, words 5, hs.seq he, by simpa [hv] using h5,
    hlen5.trans (by simpa [hv] using (sparsify_parameters_le_input n).1), ?_, ?_⟩
  · funext i
    by_cases hi : i = 266
    · subst i
      rw [hkeep _ (by decide), Function.update_self]
      simpa [ScheduleProgram.slots] using hlocal 5
    rw [Function.update_of_ne hi]
    by_cases hc : i ∈ ([1, 2, 3, 4] : List (Fin 1220))
    · rw [hclear i hc]
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · have hp := hports (1 : Fin 32)
        rw [ScheduleProgram.sharedStacks_other 1 (by decide) (by decide)] at hp
        simpa using hp.symm
      · have hp := hports (2 : Fin 32)
        rw [ScheduleProgram.sharedStacks_other 2 (by decide) (by decide)] at hp
        simpa using hp.symm
      · have hp := hports (3 : Fin 32)
        rw [ScheduleProgram.sharedStacks_other 3 (by decide) (by decide)] at hp
        simpa using hp.symm
      · have hp := hports (4 : Fin 32)
        rw [ScheduleProgram.sharedStacks_other 4 (by decide) (by decide)] at hp
        simpa using hp.symm
    rw [hkeep i hc]
    by_cases hp : ∃ j, ScheduleProgram.sharedStacks j = i
    · obtain ⟨j, rfl⟩ := hp
      rw [hlocal, hports]
      by_cases hj0 : j = 0
      · subst j
        simpa [ScheduleProgram.slots, Fin.coe_ofNat_eq_mod] using h0
      by_cases hj5 : j = 5
      · subst j
        exact (hi ScheduleProgram.sharedStacks_output).elim
      have hvj : (ScheduleProgram.sharedStacks j).val = j.val := by
        simp only [scheduleStacks_val, ite_eq_right hj0, ite_eq_right hj5]
      have hlow : 6 ≤ j.val := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Fin.ext_iff] at hc
        rw [hvj] at hc
        have hzero : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
        have hfive : j.val ≠ 5 := fun h => hj5 (Fin.ext h)
        norm_num at hc
        omega
      simp [ScheduleProgram.slots, show ¬j.val < 6 by omega, hj0]
    · exact hframe i hp
  · simp only [List.length_cons, List.length_nil] at hu
    dsimp [D] at hu
    rw [hv] at htime
    omega

structure SetupReady (k : ℕ) {n : ℕ} (F : SAT.CNF (Fin n))
    (a : State 80 1220) : Prop where
  input : a.stacks ABI.countStack = Encoding.encodeCNF F
  header : a.stacks 258 = Encoding.encodeNat n
  body : a.stacks 265 = SubexpNormalizationCorrectness.normalizedBody F
  dimension : toNat (a.stacks 267) = n
  dimension_length : (a.stacks 267).length ≤ n + 1
  schedule : toNat (a.stacks 266) = sparsifySchedule n
  threshold : toNat (a.stacks 259) =
    DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by decide)
  occurrence : toNat (a.stacks 264) = 4 * toNat (a.stacks 259) ^ (k - 1)
  blank : ∀ i, i ≠ ABI.countStack → i ≠ 258 → i ≠ 265 → i ≠ 267 →
    i ≠ 266 → i ≠ 259 → i ≠ 264 → a.stacks i = []

theorem setupAfterFrontend_eval (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ {n : ℕ} (F : SAT.CNF (Fin n))
      (binary : List Bool) (a : State 80 1220),
      FrontendReady F binary a → toNat binary = n → binary.length ≤ n →
      20 ≤ n → 0 < sparsifySchedule n → ∃ steps b,
        Eval (setupAfterFrontend k) steps a b ∧ SetupReady k F b ∧
        steps + 1 ≤ C * (Encoding.formulaBitLength F + 1) ^ 3 := by
  obtain ⟨K, hK⟩ := DisjointReuse.SparseBudgetProgram.commandCost_polynomial k
  refine ⟨9 * (216 * 10000002) + 9782 + K, by omega, ?_⟩
  intro n F binary a ha hv hlen hn hs
  have hsports : ∀ j : Fin 32, a.stacks (ScheduleProgram.sharedStacks j) =
      if j = 0 then binary else [] := by
    intro j
    by_cases h0 : j = 0
    · subst j
      simpa using ha.dimension
    rw [ite_eq_right h0]
    apply ha.blank
    · intro h
      exact scheduleStacks_off ABI.countStack (by decide) (by decide) (by decide) ⟨j, h⟩
    · intro h
      exact scheduleStacks_off 258 (by decide) (by decide) (by decide) ⟨j, h⟩
    · intro h
      exact scheduleStacks_off 265 (by decide) (by decide) (by decide) ⟨j, h⟩
    · intro h
      exact h0 (ScheduleProgram.sharedStacks.injective
        (h.trans ScheduleProgram.sharedStacks_input.symm))
  obtain ⟨t, c, s, hc, hvs, hls, hcs, ht⟩ := schedule_clear_eval n binary a hv hn
    (Encoding.formulaBitLength F + 1) hsports (frontendReady_stack_bound F binary a ha hlen)
  have hbports : ∀ j : Fin 32, c.stacks (budgetStacks j) = if j = 0 then s else [] := by
    intro j
    rw [hcs]
    by_cases h0 : j = 0
    · subst j
      rw [budgetStacks_zero, Function.update_self]
      rfl
    rw [ite_eq_right h0, Function.update_of_ne]
    · apply ha.blank
      · intro h
        exact budgetStacks_off ABI.countStack (by decide) (by decide) (by decide) (by decide) ⟨j, h⟩
      · intro h
        exact budgetStacks_off 258 (by decide) (by decide) (by decide) (by decide) ⟨j, h⟩
      · intro h
        exact budgetStacks_off 265 (by decide) (by decide) (by decide) (by decide) ⟨j, h⟩
      · intro h
        exact budgetStacks_off 267 (by decide) (by decide) (by decide) (by decide) ⟨j, h⟩
    · intro h
      apply h0
      exact budgetStacks.injective (h.trans budgetStacks_zero.symm)
  obtain ⟨u, b, M, B, hb, hu, hM, hB, hbp, hbf⟩ := budgetCall_eval k hk s c hbports
  have hframe (i : Fin 1220) (hi : 32 ≤ i.val)
      (h266 : i ≠ 266) (h259 : i ≠ 259) (h264 : i ≠ 264) :
      b.stacks i = a.stacks i := by
    rw [hbf i (budgetStacks_off i hi h266 h259 h264), hcs,
      Function.update_of_ne h266]
  have hb266 : b.stacks 266 = s := by simpa using hbp 0
  have hb259 : b.stacks 259 = M := by simpa using hbp 1
  have hb264 : b.stacks 264 = B := by simpa using hbp 2
  refine ⟨t + u, b, ?_, ?_, ?_⟩
  · exact hc.seq hb
  · constructor
    · exact (hframe _ (by decide) (by decide) (by decide) (by decide)).trans ha.input
    · exact (hframe _ (by decide) (by decide) (by decide) (by decide)).trans ha.header
    · exact (hframe _ (by decide) (by decide) (by decide) (by decide)).trans ha.body
    · rw [hframe _ (by decide) (by decide) (by decide) (by decide), ha.dimension]
      exact hv
    · rw [hframe _ (by decide) (by decide) (by decide) (by decide), ha.dimension]
      exact hlen.trans (Nat.le_succ _)
    · rw [hb266]
      exact hvs
    · rw [hb259, hM, hvs]
    · rw [hb264, hb259]
      exact hB
    · intro i hi h258 h265 h267 h266 h259 h264
      by_cases hp : ∃ j, budgetStacks j = i
      · obtain ⟨j, rfl⟩ := hp
        rw [hbp]
        split_ifs with h0 h1 h2
        · subst j
          exact (h266 budgetStacks_zero).elim
        · subst j
          exact (h259 budgetStacks_one).elim
        · subst j
          exact (h264 budgetStacks_two).elim
        · rfl
      · rw [hbf i hp, hcs, Function.update_of_ne h266]
        exact ha.blank i hi h258 h265 h267
  · let P := (Encoding.formulaBitLength F + 1) ^ 3
    have hLn := Encoding.numVariables_le_formulaBitLength F
    have hlinear : Encoding.formulaBitLength F + 1 ≤ P := Nat.le_self_pow (by decide) _
    have hone : 1 ≤ P := Nat.one_le_pow' 3 _
    have harg : n + binary.length + 6 ≤ 6 * (Encoding.formulaBitLength F + 1) := by omega
    have hcube := Nat.pow_le_pow_left harg 3
    rw [mul_pow] at hcube
    have hschedule : t ≤ (9 * (216 * 10000002) + 9780) * P := by
      dsimp [P] at hlinear hone ⊢
      nlinarith only [ht, hcube, hlinear, hone]
    have hpositive : 0 < toNat s := by omega
    have hbudget := hK s hpositive
    have hsword : (s.length + 1) ^ 3 ≤ P :=
      Nat.pow_le_pow_left (by omega) 3
    have hbudget' : u ≤ (K + 1) * P := by
      have hmul := Nat.mul_le_mul_left K hsword
      nlinarith only [hu, hbudget, hmul, hone]
    change _ ≤ (9 * (216 * 10000002) + 9782 + K) * P
    nlinarith only [hschedule, hbudget', hone]


theorem setup_eval (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ {n : ℕ} (F : SAT.CNF (Fin n)), 20 ≤ n →
      0 < sparsifySchedule n → ∃ steps b,
        Eval (setupCommand k) steps (StructuredProgram.ioState ABI.countStack
          (Encoding.encodeCNF F)) b ∧ SetupReady k F b ∧
        steps + 1 ≤ C * (Encoding.formulaBitLength F + 1) ^ 3 := by
  obtain ⟨C, hC, htail⟩ := setupAfterFrontend_eval k hk
  refine ⟨4000 + C, by omega, ?_⟩
  intro n F hn hs
  obtain ⟨binary, f, a, hv, hlen, hf, he, ha⟩ := frontend_eval F
  obtain ⟨t, b, ht, hb, htime⟩ := htail F binary a ha hv hlen hn hs
  refine ⟨f+t, b, he.seq ht, hb, ?_⟩
  have hpow : (Encoding.formulaBitLength F + 1) ^ 2 ≤
      (Encoding.formulaBitLength F + 1) ^ 3 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hfront := (hf.trans (frontendBound_polynomial F)).trans
    (Nat.mul_le_mul_left 4000 hpow)
  nlinarith only [hfront, htime]

theorem setup_trace_space (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ {n : ℕ} (F : SAT.CNF (Fin n)), 20 ≤ n →
      0 < sparsifySchedule n → ∃ steps b,
        Trace (setupProgram k) steps (initial (setupProgram k) (Encoding.encodeCNF F))
          (b.withPC none) ∧ SetupReady k F b ∧
        steps ≤ C * (Encoding.formulaBitLength F + 1) ^ 3 ∧
        ∀ prefixSteps intermediate, prefixSteps ≤ steps →
          Trace (setupProgram k) prefixSteps
            (initial (setupProgram k) (Encoding.encodeCNF F)) intermediate →
          dataBits intermediate ≤ (C + 1) * (Encoding.formulaBitLength F + 1) ^ 3 ∧
          ∀ i, (intermediate.stacks i).length ≤
            (C + 1) * (Encoding.formulaBitLength F + 1) ^ 3 := by
  obtain ⟨C, hC, hrun⟩ := setup_eval k hk
  refine ⟨C, hC, ?_⟩
  intro n F hn hs
  obtain ⟨steps, b, he, hb, ht⟩ := hrun F hn hs
  refine ⟨steps + 1, b, compiled_halt_trace he ABI.countStack ABI.answerStack, hb, ht, ?_⟩
  intro prefixSteps intermediate hp htrace
  have hgrowth := trace_dataBits (setupProgram k) htrace
  rw [initial_dataBits] at hgrowth
  have hlinear : Encoding.formulaBitLength F ≤ (Encoding.formulaBitLength F + 1) ^ 3 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have htotal : dataBits intermediate ≤ (C + 1) *
      (Encoding.formulaBitLength F + 1) ^ 3 := by
    change dataBits intermediate ≤ Encoding.formulaBitLength F + prefixSteps at hgrowth
    nlinarith only [hgrowth, hlinear, hp.trans ht]
  refine ⟨htotal, fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => Nat.zero_le ((intermediate.stacks j).length))
    (Finset.mem_univ i)).trans htotal

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
