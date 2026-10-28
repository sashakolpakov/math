import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram

namespace OAI.Algorithms

/-! Concrete composition of score selection and packed assignment update. -/

namespace SubexponentialSAT.Subexp.SequentialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem lookup_split {A : Type*} (xs : List A) (k : ℕ) (x : A)
    (h : xs[k]? = some x) :
    ∃ before after, xs = before ++ x :: after ∧ before.length = k := by
  induction xs generalizing k with
  | nil => simp at h
  | cons a xs ih =>
      cases k with
      | zero =>
          have ha : a = x := by simpa using h
          subst a
          exact ⟨[], xs, rfl, rfl⟩
      | succ k =>
          obtain ⟨before, after, hs, hl⟩ := ih k (by simpa using h)
          exact ⟨a :: before, after, by simp [hs], by simp [hl]⟩

theorem sum_scores_le {A : Type*} (xs : List A) (score : A → ℕ) (S : ℕ)
    (h : ∀ x ∈ xs, score x ≤ S) : (xs.map score).sum ≤ xs.length * S := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha := h a (by simp)
      have ht := ih (fun x hx => h x (by simp [hx]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

def minimumBudget (q S : ℕ) : ℕ := 500 * (q * (S + 1)) ^ 2
def recordBudget (q S : ℕ) : ℕ := 2 * (q * S) + 2 * q + 1
def updateBudget (q total width : ℕ) : ℕ :=
  (q * (14 * width + 10) + 15 * width + 16) +
    ((7 * total + 5) + (total * (14 * width + 10) + 20 * width + 21))
def selectionBudget (q S total width : ℕ) : ℕ :=
  9 + minimumBudget q S + updateBudget q total width +
    9 * (2 * (recordBudget q S + minimumBudget q S + width) + 3) + 2

def afterProcessed (d : Data) : Data :=
  ⟨Function.update d.regs 9 false,
    Function.update d.stacks 19 (false :: d.stacks 19)⟩

theorem incrementProcessed_eval (d : Data) :
    Eval incrementProcessed 2 d (afterProcessed d) := by
  have h := Eval.seq (Eval.base (StructuredProgram.Eval.atom (.set 9 false) d))
    (Eval.base (StructuredProgram.Eval.atom (.push 19 9) _))
  simpa [incrementProcessed, atom, afterProcessed, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h

def cleanPorts : List (Fin 48) := [0, 1, 2, 3, 4, 5, 6, 7, 12]

theorem scratch_partition (j : Fin 48) (hj : j ∈ scratchPorts) :
    j ∈ cleanPorts ∨ 13 ≤ j.val ∧ j.val ≤ 18 := by
  exact (show ∀ j : Fin 48, j ∈ scratchPorts →
    j ∈ cleanPorts ∨ 13 ≤ j.val ∧ j.val ≤ 18 by decide) j hj

/-- The concrete selection/update code needs only a prepared score stream;
every following operation is an actual fixed machine subroutine. -/
theorem selectAndUpdate_eval {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (hwidth : ∀ x, (encode x).length = (encode a).length)
    (score : A → ℕ) (S total n : ℕ) (fixed : List A)
    (hscore : ∀ x ∈ a :: tail, score x ≤ S) (hfixed : fixed.length ≤ total)
    (base d : Data) (hm : Memory encode a tail (n + 1) fixed base.stacks)
    (hs : d.stacks 0 = ProgramEncoding.encodeRecords
      ((a :: tail).map (fun x => UnaryCompare.encode (score x))))
    (hf : ∀ j : Fin 48, j.val < 20 → j ≠ 0 → d.stacks j = base.stacks j) :
    ∃ t ≤ selectionBudget (a :: tail).length S total (encode a).length,
      ∃ e : Data,
        Eval selectAndUpdate t d e ∧
        Memory encode a tail n
          (NaturalAssignment.chooseMinNat score a tail :: fixed) e.stacks ∧
        e.stacks 11 = base.stacks 11 ∧
        (∀ j : Fin 48, 20 ≤ j.val → e.stacks j = d.stacks j) := by
  let q := (a :: tail).length
  let w := (encode a).length
  let chosen := NaturalAssignment.chooseMinNat score a tail
  let assigned := fixed.reverse.map encode
  let rest := (List.replicate n (encode a)).flatten
  have hsum := sum_scores_le tail score S (fun x hx => hscore x (by simp [hx]))
  have hhead := hscore a (by simp)
  have hminBound : 500 * (score a + (tail.map score).sum + tail.length + 1) ^ 2 ≤
      minimumBudget q S := by
    unfold minimumBudget q
    gcongr
    simp only [List.length_cons]
    nlinarith
  have hrecord : (d.stacks 0).length ≤ recordBudget q S := by
    rw [hs, ProgramEncoding.encodeRecords_length]
    simp only [List.map_map, Function.comp_def, UnaryCompare.encode_length,
      List.map_cons, List.sum_cons, List.length_map, List.length_cons]
    unfold recordBudget q
    simp only [List.length_cons]
    nlinarith
  obtain ⟨r, hr, hrs, hrr⟩ := resetRegisters_eval d
  have hrinput : r.stacks 0 = d.stacks 0 := congrFun hrs 0
  have hrsmall (i : Fin 8) (hi : i ≠ 0) : r.stacks (minimumStacks i) = [] := by
    rw [hrs, hf (minimumStacks i) (by change i.val < 20; omega)
      (by
        intro h
        have hv := congrArg (fun j : Fin 48 => j.val) h
        exact hi (Fin.ext hv))]
    exact hm.scratch _ (by
      fin_cases i <;> simp_all [minimumStacks, scratchPorts])
  obtain ⟨m, hmb, middle, k, hk, hmin, hki, hlookup, hframe, _, hsmall⟩ :=
    minimum_eval score a tail r hrr (hrinput.trans hs) hrsmall
  have hmiddle (j : Fin 48) (hj : 8 ≤ j.val) (hj20 : j.val < 20) :
      middle.stacks j = base.stacks j := by
    rw [hframe j hj, hrs, hf j hj20 (by intro h; subst j; omega)]
  obtain ⟨before, after, hsplit, hbeforelen⟩ := lookup_split (a :: tail) k chosen hlookup
  have hwidth' (x : A) : (encode x).length = (middle.stacks 10).length := by
    rw [hmiddle 10 (by decide) (by decide), hm.width, hwidth]
  have hbefore : ∀ row ∈ before.map encode, row.length = (middle.stacks 10).length := by
    intro row hrow
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hrow
    exact hwidth' x
  have hassigned : ∀ row ∈ assigned, row.length = (middle.stacks 10).length := by
    intro row hrow
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hrow
    exact hwidth' x
  have hcandidate : middle.stacks 9 =
      (before.map encode).flatten ++ (encode chosen ++ (after.map encode).flatten) := by
    rw [hmiddle 9 (by decide) (by decide), hm.alphabet, hsplit]
    simp [List.map_append, List.flatten_append, List.flatten_cons]
  have hassign : middle.stacks 8 = assigned.flatten ++ (encode a ++ rest) := by
    rw [hmiddle 8 (by decide) (by decide), hm.assignment]
    simp [assigned, rest, List.replicate_succ, List.flatten_append, List.flatten_cons]
  have hc (j : Fin 48) (hj : j ∈ scratchPorts) (hlo : 8 ≤ j.val) (hhi : j.val < 20) :
      middle.stacks j = [] := by
    rw [hmiddle j hlo hhi]
    exact hm.scratch j hj
  have hup := wordUpdate_eval middle (before.map encode) assigned (encode chosen) (encode a)
    (after.map encode).flatten rest hcandidate hassign
    (by simpa [hbeforelen] using hki)
    (by simpa [hmiddle 19 (by decide) (by decide), assigned] using hm.processed)
    hbefore hassigned (hwidth' chosen) (hwidth' a)
    (hc 12 (by decide) (by decide) (by decide))
    (hc 13 (by decide) (by decide) (by decide))
    (hc 14 (by decide) (by decide) (by decide))
    (hc 15 (by decide) (by decide) (by decide))
    (hc 16 (by decide) (by decide) (by decide))
    (hc 17 (by decide) (by decide) (by decide))
    (hc 18 (by decide) (by decide) (by decide))
  let updated := afterWordUpdate middle assigned (encode chosen) rest
  let cb := recordBudget q S + minimumBudget q S + w
  have hcleanBound : ∀ j ∈ cleanPorts, (updated.stacks j).length ≤ cb := by
    intro j hj
    have hcases : j.val < 8 ∨ j = 12 :=
      (show ∀ j : Fin 48, j ∈ cleanPorts → j.val < 8 ∨ j = 12 by decide) j hj
    rcases hcases with hj | rfl
    · by_cases h7 : j = 7
      · simp [updated, h7, cb]
      · have hj12 : j ≠ 12 := by intro h; subst j; omega
        have hj8 : j ≠ 8 := by intro h; subst j; omega
        have hh := hsmall j hj
        rw [hrinput] at hh
        simp only [updated, Function.update_of_ne hj8,
          Function.update_of_ne hj12, Function.update_of_ne h7]
        unfold cb
        omega
    · simp [updated, cb, w, hwidth]
  obtain ⟨c, hcb, cleaned, hclean, hcleaned⟩ := cleanAuxiliary_eval updated cb hcleanBound
  let final := afterProcessed cleaned
  have hfinal : Memory encode a tail n (chosen :: fixed) final.stacks := by
    constructor
    · rw [show final.stacks 8 = cleaned.stacks 8 by simp [final, afterProcessed]]
      rw [hcleaned]
      simp [ updated, assigned, rest, List.reverse_cons,
        List.map_append, List.flatten_append, List.flatten_cons, List.append_assoc]
    · rw [show final.stacks 9 = cleaned.stacks 9 by simp [final, afterProcessed], hcleaned]
      simpa [cleanPorts, updated, afterWordUpdate, hmiddle 9 (by decide) (by decide)]
        using hm.alphabet
    · rw [show final.stacks 10 = cleaned.stacks 10 by simp [final, afterProcessed], hcleaned]
      simpa [cleanPorts, updated, afterWordUpdate, hmiddle 10 (by decide) (by decide)]
        using hm.width
    · simp [final, afterProcessed, hcleaned, updated,
        hmiddle 19 (by decide) (by decide), hm.processed]
    · intro j hj
      rcases scratch_partition j hj with hjclean | hjhigh
      · have hj19 : j ≠ 19 := by
          intro heq
          subst j
          simp [cleanPorts] at hjclean
        simp only [final, afterProcessed, Function.update_of_ne hj19, hcleaned]
        exact ite_eq_left hjclean
      · have hj19 : j ≠ 19 := by intro heq; subst j; omega
        have hj7 : j ≠ 7 := by intro heq; subst j; omega
        have hj8 : j ≠ 8 := by intro heq; subst j; omega
        have hj12 : j ≠ 12 := by intro heq; subst j; omega
        simp only [final, afterProcessed, Function.update_of_ne hj19, hcleaned]
        split
        · rfl
        · simp only [updated, Function.update_of_ne hj8,
            Function.update_of_ne hj12, Function.update_of_ne hj7]
          rw [hmiddle j (by omega) (by omega)]
          exact hm.scratch j hj
  have hcounter : final.stacks 11 = base.stacks 11 := by
    simp [final, afterProcessed, hcleaned, updated,
      hmiddle 11 (by decide) (by decide)]
  have hhigh : ∀ j : Fin 48, 20 ≤ j.val → final.stacks j = d.stacks j := by
    intro j hj
    have hj19 : j ≠ 19 := by intro heq; subst j; omega
    have hj12 : j ≠ 12 := by intro heq; subst j; omega
    have hj8 : j ≠ 8 := by intro heq; subst j; omega
    have hj7 : j ≠ 7 := by intro heq; subst j; omega
    have hnot : j ∉ cleanPorts := by
      intro hm
      have hc := (show ∀ j : Fin 48, j ∈ cleanPorts → j.val < 13 by decide) j hm
      omega
    change j ∉ ([0, 1, 2, 3, 4, 5, 6, 7, 12] : List (Fin 48)) at hnot
    simp only [final, afterProcessed, Function.update_of_ne hj19, hcleaned, ite_eq_right hnot,
      updated, Function.update_of_ne hj8,
      Function.update_of_ne hj12, Function.update_of_ne hj7]
    rw [hframe j (by omega), hrs]
  let updateTime := (before.map encode).length * (14 * (middle.stacks 10).length + 10) +
          15 * (middle.stacks 10).length + 16 +
        (7 * assigned.length + 5 +
          (assigned.length * (14 * (middle.stacks 10).length + 10) +
            20 * (middle.stacks 10).length + 21))
  have hupdateBound : updateTime ≤ updateBudget q total w := by
    have hbeforeq : before.length ≤ q := by
      rw [hbeforelen]
      exact Nat.le_of_lt hk
    simp only [updateTime, List.length_map, assigned, List.length_reverse]
    rw [hmiddle 10 (by decide) (by decide), hm.width]
    unfold updateBudget w
    gcongr
  refine ⟨9 + (m + (updateTime + (c + 2))), ?_, final, ?_, hfinal, hcounter, hhigh⟩
  · change 9 + (m + (updateTime + (c + 2))) ≤ selectionBudget q S total w
    unfold selectionBudget
    change c ≤ 9 * (2 * (recordBudget q S + minimumBudget q S + w) + 3) at hcb
    omega
  · exact hr.seq (hmin.seq (hup.seq (hclean.seq (incrementProcessed_eval cleaned))))

/-- The remaining integration boundary is a real execution of the supplied
fixed score-stream program. It preserves the assignment and controller ports
while writing one framed unary score per candidate to stack zero. -/
abbrev ScoreBuilderRefines {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (evaluate : ℕ → List A → ℕ) (builder : Cmd 16 48) (budget total : ℕ)
    (environment : Fin 48 → List Bool) : Prop :=
  ∀ (n : ℕ) (fixed : List A) (d : Data),
    n + 1 + fixed.length = total →
    Memory encode a tail (n + 1) fixed d.stacks →
    (d.stacks 11).length = n →
    HighState environment d.stacks →
    ∃ t ≤ budget, ∃ e : Data,
      Eval builder t d e ∧
      e.stacks 0 = ProgramEncoding.encodeRecords
        ((a :: tail).map (fun x => UnaryCompare.encode (evaluate n (x :: fixed)))) ∧
      (∀ j : Fin 48, j.val < 20 → j ≠ 0 → e.stacks j = d.stacks j) ∧
      HighState environment e.stacks

theorem stepRefines_of_scoreBuilder {A : Type*} (encode : A → List Bool) (a : A)
    (tail : List A) (evaluate : ℕ → List A → ℕ)
    (builder : Cmd 16 48) (scoreCost S total : ℕ)
    (environment : Fin 48 → List Bool)
    (hwidth : ∀ x, (encode x).length = (encode a).length)
    (hscore : ∀ n fixed x, n + 1 + fixed.length ≤ total → x ∈ a :: tail →
      evaluate n (x :: fixed) ≤ S)
    (hbuilder : ScoreBuilderRefines encode a tail evaluate builder scoreCost total environment) :
    StepRefines encode a tail evaluate builder
      (scoreCost + selectionBudget (a :: tail).length S total (encode a).length) total environment := by
  intro n fixed d hsize hm hcounter hcontext
  obtain ⟨t, ht, prepared, hp, hs, hf, hprepared⟩ := hbuilder n fixed d hsize hm hcounter hcontext
  obtain ⟨m, hmb, e, he, hmem, hc, hhigh⟩ := selectAndUpdate_eval encode a tail hwidth
    (fun x => evaluate n (x :: fixed)) S total n fixed
    (fun x hx => hscore n fixed x hsize.le hx) (by omega) d prepared hm hs hf
  refine ⟨t + m, by omega, e, hp.seq he, hmem, ?_, ?_⟩
  · rw [hc]
    exact hcounter
  · intro j hj
    rw [hhigh j hj]
    exact hprepared j hj

/-- The complete controller cost is polynomial once the actual fixed score
builder has its bounded execution theorem. All selection and update costs are
already included in the explicit selectionBudget polynomial. -/
theorem program_of_scoreBuilder {A : Type*} (encode : A → List Bool) (a : A)
    (tail : List A) (evaluate : ℕ → List A → ℕ)
    (builder : Cmd 16 48) (scoreCost S total : ℕ)
    (environment : Fin 48 → List Bool)
    (hwidth : ∀ x, (encode x).length = (encode a).length)
    (hscore : ∀ n fixed x, n + 1 + fixed.length ≤ total → x ∈ a :: tail →
      evaluate n (x :: fixed) ≤ S)
    (hbuilder : ScoreBuilderRefines encode a tail evaluate builder scoreCost total environment)
    (d : Data) (hm : Memory encode a tail total [] d.stacks)
    (hc : (d.stacks 11).length = total) (hcontext : HighState environment d.stacks) :
    ∃ e : Data, RunsIn (program builder)
      (total * (scoreCost +
        selectionBudget (a :: tail).length S total (encode a).length + 3) + 3)
      (d.withPC (some (program builder).entry)) (e.withPC none) ∧
      e.stacks 8 =
        ((NaturalAssignment.assignNat a tail evaluate total []).reverse.map encode).flatten := by
  exact program_runsIn encode a tail evaluate builder
    (scoreCost + selectionBudget (a :: tail).length S total (encode a).length) total
    environment
    (stepRefines_of_scoreBuilder encode a tail evaluate builder scoreCost S total
      environment hwidth hscore hbuilder) total [] d (by simp) hm hc hcontext

/-- The controller's input encoding: packed alphabet and initial assignment,
unary width and remaining count, and a separate runtime environment. -/
def initialData {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (total : ℕ) (environment : Fin 48 → List Bool) : Data :=
  ⟨fun _ => false, fun j =>
    if j = 8 then (List.replicate total (encode a)).flatten
    else if j = 9 then ((a :: tail).map encode).flatten
    else if j = 10 then List.replicate (encode a).length false
    else if j = 11 then List.replicate total false
    else if 20 ≤ j.val then environment j else []⟩

theorem initialData_memory {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (total : ℕ) (environment : Fin 48 → List Bool) :
    Memory encode a tail total [] (initialData encode a tail total environment).stacks := by
  constructor
  · simp [initialData]
  · simp [initialData]
  · simp [initialData]
  · simp [initialData,
      show (19 : Fin 48) ≠ 8 by decide, show (19 : Fin 48) ≠ 9 by decide,
      show (19 : Fin 48) ≠ 10 by decide, show (19 : Fin 48) ≠ 11 by decide
      ]
  · intro j hj
    have hn : j ≠ 8 ∧ j ≠ 9 ∧ j ≠ 10 ∧ j ≠ 11 ∧ j.val < 20 :=
      (show ∀ j : Fin 48, j ∈ scratchPorts →
        j ≠ 8 ∧ j ≠ 9 ∧ j ≠ 10 ∧ j ≠ 11 ∧ j.val < 20 by decide) j hj
    simp [initialData, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, Nat.not_le.mpr hn.2.2.2.2]

theorem initialData_high {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (total : ℕ) (environment : Fin 48 → List Bool) :
    HighState environment (initialData encode a tail total environment).stacks := by
  intro j hj
  have h8 : j ≠ 8 := by intro h; subst j; omega
  have h9 : j ≠ 9 := by intro h; subst j; omega
  have h10 : j ≠ 10 := by intro h; subst j; omega
  have h11 : j ≠ 11 := by intro h; subst j; omega
  simp [initialData, h8, h9, h10, h11, hj]

theorem program_initial_of_scoreBuilder {A : Type*} (encode : A → List Bool) (a : A)
    (tail : List A) (evaluate : ℕ → List A → ℕ)
    (builder : Cmd 16 48) (scoreCost S total : ℕ)
    (environment : Fin 48 → List Bool)
    (hwidth : ∀ x, (encode x).length = (encode a).length)
    (hscore : ∀ n fixed x, n + 1 + fixed.length ≤ total → x ∈ a :: tail →
      evaluate n (x :: fixed) ≤ S)
    (hbuilder : ScoreBuilderRefines encode a tail evaluate builder scoreCost total environment) :
    ∃ e : Data, RunsIn (program builder)
      (total * (scoreCost +
        selectionBudget (a :: tail).length S total (encode a).length + 3) + 3)
      ((initialData encode a tail total environment).withPC (some (program builder).entry))
      (e.withPC none) ∧
      e.stacks 8 =
        ((NaturalAssignment.assignNat a tail evaluate total []).reverse.map encode).flatten := by
  exact program_of_scoreBuilder encode a tail evaluate builder scoreCost S total environment
    hwidth hscore hbuilder _ (initialData_memory encode a tail total environment)
    (by simp [initialData]) (initialData_high encode a tail total environment)

section NaturalScores

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpTypeVariance SubexponentialSAT.SlotAssignment

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (P : SubexponentialSAT.Factor.Pattern V E) {r Q Δ : ℕ} [NeZero r] (slots : SlotMap P Δ)

omit [Fintype V] [NeZero r] in
/-- Specialization to the actual local natural-number scores. The output is
exactly the encoded word list defining naturalAssignment/computedAssignment. -/
theorem naturalValues_program
    (encode : Word r Q → List Bool) (a : Word r Q) (tail : List (Word r Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (indices : List (SeedIndex V E Δ))
    (builder : Cmd 16 48) (scoreCost : ℕ) (environment : Fin 48 → List Bool)
    (hwidth : ∀ x, (encode x).length = (encode a).length)
    (hbuilder : ScoreBuilderRefines encode a tail
      (NaturalAssignment.sequentialNumerator P slots (a :: tail) vertices indices a)
      builder scoreCost indices.length environment) :
    ∃ e : Data, RunsIn (program builder)
      (indices.length * (scoreCost + selectionBudget (a :: tail).length
        (vertices.length ^ 2 * (blockSize r Q Δ) ^ 2) indices.length (encode a).length + 3) + 3)
      ((initialData encode a tail indices.length environment).withPC (some (program builder).entry))
      (e.withPC none) ∧
      e.stacks 8 =
        ((NaturalAssignment.naturalValues P slots a tail vertices indices).reverse.map encode).flatten := by
  exact program_initial_of_scoreBuilder encode a tail
    (NaturalAssignment.sequentialNumerator P slots (a :: tail) vertices indices a)
    builder scoreCost (vertices.length ^ 2 * (blockSize r Q Δ) ^ 2) indices.length
    environment hwidth
    (fun n fixed x _ _ => NaturalAssignment.sequentialNumerator_le P slots
      (a :: tail) haNodup haFull vertices indices a n (x :: fixed)) hbuilder

end NaturalScores

end SubexponentialSAT.Subexp.SequentialProgram

end OAI.Algorithms
