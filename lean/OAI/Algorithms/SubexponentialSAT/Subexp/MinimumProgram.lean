import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.UnaryCompare
import OAI.Algorithms.SubexponentialSAT.Subexp.NaturalAssignment

namespace OAI.Algorithms

/-!
# A fixed program selecting the first minimum unary score

The input is a framed list of prepared unary scores. Scores are represented
by list lengths. The program returns the selected zero-based index in unary.
All control, registers, and stack ports are fixed independently of the input.
-/

namespace SubexponentialSAT.Subexp.MinimumProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StackRoutines

abbrev Data := State 9 8

def ports : RecordPrograms.Ports 9 8 where
  tag := 0
  present := 1
  found := 2
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev atom (a : StructuredProgram.Atom 9 8) : Cmd 9 8 := .base (.atom a)

abbrev clear (dst : Fin 8) : Cmd 9 8 := .call (clearProgram dst 3 4)
abbrev copy (src dst : Fin 8) : Cmd 9 8 := .call (copyProgram src dst 5 3 4)

def afterClear (d : Data) (dst : Fin 8) : Data :=
  ⟨readRegs d.regs 3 4 none, clearStacks dst d.stacks⟩

def afterCopy (d : Data) (src dst : Fin 8) : Data :=
  ⟨readRegs d.regs 3 4 none, copyStacks src dst d.stacks⟩

theorem clear_eval (d : Data) (dst : Fin 8) :
    Eval (clear dst) (2 * (d.stacks dst).length + 3) d (afterClear d dst) :=
  .call _ (ListRegisterProgram.clear_run dst 3 4 d.regs d.stacks)

theorem copy_eval (d : Data) (src dst : Fin 8)
    (hsd : src ≠ dst) (hs : src ≠ 5) (hd : (5 : Fin 8) ≠ dst)
    (htmp : d.stacks 5 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (afterCopy d src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 5 3 4 hsd hs hd
    (by decide) d.regs d.stacks htmp)

def compareRegs : Fin 4 → Fin 9 := Fin.natAdd 5
def compareStacks (i : Fin 2) : Fin 8 := if i = 0 then 3 else 4

theorem compareRegs_injective : Function.Injective compareRegs := by
  intro i j h
  exact (Fin.natAdd_inj 5).mp h

theorem compareStacks_injective : Function.Injective compareStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [compareStacks]

abbrev comparator : Program 9 8 7 :=
  ProgramLinking.liftProgram UnaryCompare.program compareRegs compareStacks

private theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

private theorem embed_restrict (d : Data) :
    embedState compareRegs compareStacks d
      ⟨fun i => d.regs (compareRegs i), fun i => d.stacks (compareStacks i)⟩ = d := by
  apply state_ext
  · funext j
    by_cases h : ∃ i, compareRegs i = j
    · obtain ⟨i, rfl⟩ := h
      exact embedState_register _ _ _ _ compareRegs_injective i
    · exact embedState_register_frame _ _ _ _ j h
  · funext j
    by_cases h : ∃ i, compareStacks i = j
    · obtain ⟨i, rfl⟩ := h
      exact embedState_stack _ _ _ _ compareStacks_injective i
    · exact embedState_stack_frame _ _ _ _ j h

/-- A genuine call to the destructive comparator, including all required
framing and bounds on the two residual scratch stacks. -/
theorem compare_eval (d : Data) :
    ∃ n ≤ 4 * min (d.stacks 3).length (d.stacks 4).length + 6, ∃ e : Data,
      Eval (.call comparator) n d e ∧
      e.regs 8 = decide ((d.stacks 3).length ≤ (d.stacks 4).length) ∧
      (∀ j : Fin 9, j.val < 5 → e.regs j = d.regs j) ∧
      (∀ j : Fin 8, j ≠ 3 → j ≠ 4 → e.stacks j = d.stacks j) ∧
      (e.stacks 3).length ≤ (d.stacks 3).length ∧
      (e.stacks 4).length ≤ (d.stacks 4).length := by
  obtain ⟨n, hn, c, ht, hp, hout⟩ :=
    UnaryCompare.runs (fun i => d.regs (compareRegs i)) (d.stacks 3) (d.stacks 4)
  let a : State 4 2 :=
    ⟨fun i => d.regs (compareRegs i), fun i => d.stacks (compareStacks i)⟩
  let b : State 4 2 := ⟨c.regs, c.stacks⟩
  let e := embedState compareRegs compareStacks d b
  have ha : embedState compareRegs compareStacks d a = d := embed_restrict d
  have ht' : Trace UnaryCompare.program n
      (a.withPC (some UnaryCompare.program.entry)) (b.withPC none) := by
    have hb : b.withPC none = c := by
      cases c
      simp_all [b, StructuredProgram.State.withPC]
    rw [hb]
    convert ht using 1
    apply congrArg (fun stk =>
      (⟨some 0, fun i => d.regs (compareRegs i), stk⟩ : Cfg 4 2 7))
    funext i
    fin_cases i <;> rfl
  have he := eval_call_lifted UnaryCompare.program compareRegs compareStacks d
    compareRegs_injective compareStacks_injective ht'
  refine ⟨n, hn, e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ha, comparator] using he
  · change (embedState compareRegs compareStacks d b).regs (compareRegs 3) = _
    rw [embedState_register _ _ _ _ compareRegs_injective]
    exact hout
  · intro j hj
    apply embedState_register_frame
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change 5 + i.val = j.val at hv
    omega
  · intro j h3 h4
    apply embedState_stack_frame
    rintro ⟨i, hi⟩
    fin_cases i <;> simp_all [compareStacks]
  · change ((embedState compareRegs compareStacks d b).stacks (compareStacks 0)).length ≤ _
    rw [embedState_stack _ _ _ _ compareStacks_injective]
    exact UnaryCompare.trace_length_le ht 0
  · change ((embedState compareRegs compareStacks d b).stacks (compareStacks 1)).length ≤ _
    rw [embedState_stack _ _ _ _ compareStacks_injective]
    exact UnaryCompare.trace_length_le ht 1

abbrev increment : Cmd 9 8 :=
  .seq (atom (.set 3 false)) (atom (.push 6 3))

def afterIncrement (d : Data) : Data :=
  ⟨Function.update d.regs 3 false, Function.update d.stacks 6 (false :: d.stacks 6)⟩

theorem increment_eval (d : Data) : Eval increment 2 d (afterIncrement d) := by
  have h := Eval.seq (Eval.base (StructuredProgram.Eval.atom (.set 3 false) d))
    (Eval.base (StructuredProgram.Eval.atom (.push 6 3) _))
  simpa [increment, atom, afterIncrement, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h

abbrev cleanup : Cmd 9 8 :=
  .seq (clear 1) (.seq (clear 3) (.seq (clear 4) increment))

def afterCleanup (d : Data) : Data :=
  afterIncrement (afterClear (afterClear (afterClear d 1) 3) 4)

theorem cleanup_eval (d : Data) :
    Eval cleanup
      (2 * (d.stacks 1).length + 2 * (d.stacks 3).length +
        2 * (d.stacks 4).length + 11) d (afterCleanup d) := by
  have h := Eval.seq (clear_eval d 1)
    (Eval.seq (clear_eval (afterClear d 1) 3)
      (Eval.seq (clear_eval (afterClear (afterClear d 1) 3) 4)
        (increment_eval (afterClear (afterClear (afterClear d 1) 3) 4))))
  convert h using 1 <;> simp [ afterCleanup, afterClear, clearStacks] ; omega

abbrev replaceBest : Cmd 9 8 :=
  .seq (clear 2) (.seq (copy 1 2) (.seq (clear 7) (copy 6 7)))

def afterReplace (d : Data) : Data :=
  afterCopy (afterClear (afterCopy (afterClear d 2) 1 2) 7) 6 7

theorem replaceBest_eval (d : Data) (htmp : d.stacks 5 = []) :
    Eval replaceBest
      (2 * (d.stacks 2).length + 7 * (d.stacks 1).length +
        2 * (d.stacks 7).length + 7 * (d.stacks 6).length + 16)
      d (afterReplace d) := by
  have h1 := clear_eval d 2
  have h2 := copy_eval (afterClear d 2) 1 2 (by decide) (by decide) (by decide)
    (by simpa [afterClear, clearStacks] using htmp)
  have h3 := clear_eval (afterCopy (afterClear d 2) 1 2) 7
  have h4 := copy_eval (afterClear (afterCopy (afterClear d 2) 1 2) 7) 6 7
    (by decide) (by decide) (by decide)
    (by simpa [afterClear, afterCopy, clearStacks, copyStacks] using htmp)
  convert Eval.seq h1 (Eval.seq h2 (Eval.seq h3 h4)) using 1 <;>
    simp [ afterReplace, afterClear, afterCopy, clearStacks, copyStacks] ; omega

abbrev callback : Cmd 9 8 :=
  .seq (copy 2 3) (.seq (copy 1 4)
    (.seq (.call comparator)
      (.seq (.ite 8 (.base .skip) replaceBest) cleanup)))

/-- Invariants at record boundaries. The score bound is independent of how
many records remain, because the stored best score only decreases. -/
def Invariant (M : ℕ) (d : Data) : Prop :=
  d.stacks 3 = [] ∧ d.stacks 4 = [] ∧ d.stacks 5 = [] ∧
    (d.stacks 2).length ≤ M ∧ (d.stacks 7).length ≤ (d.stacks 6).length

def best (d : Data) : ℕ × ℕ := ((d.stacks 2).length, (d.stacks 7).length)
def index (d : Data) : ℕ := (d.stacks 6).length

def pick (a b : ℕ × ℕ) : ℕ × ℕ := if a.1 ≤ b.1 then a else b

def scan (current : ℕ × ℕ) (next : ℕ) : List (List Bool) → ℕ × ℕ
  | [] => current
  | bits :: rest => scan (pick current (bits.length, next)) (next + 1) rest

def tagged (next : ℕ) : List (List Bool) → List (ℕ × ℕ)
  | [] => []
  | bits :: rest => (bits.length, next) :: tagged (next + 1) rest

theorem pick_assoc (a b c : ℕ × ℕ) : pick (pick a b) c = pick a (pick b c) := by
  by_cases hab : a.1 ≤ b.1 <;> by_cases hbc : b.1 ≤ c.1 <;>
    by_cases hac : a.1 ≤ c.1 <;> simp [pick, hab, hbc, hac] <;> omega

theorem choose_pick (a b : ℕ × ℕ) (xs : List (ℕ × ℕ)) :
    NaturalAssignment.chooseMinNat Prod.fst (pick a b) xs =
      pick a (NaturalAssignment.chooseMinNat Prod.fst b xs) := by
  cases xs with
  | nil => rfl
  | cons c cs =>
      change pick (pick a b) (NaturalAssignment.chooseMinNat Prod.fst c cs) =
        pick a (pick b (NaturalAssignment.chooseMinNat Prod.fst c cs))
      exact pick_assoc _ _ _

theorem scan_eq_chooseMin (current : ℕ × ℕ) (next : ℕ) (records : List (List Bool)) :
    scan current next records =
      NaturalAssignment.chooseMinNat Prod.fst current (tagged next records) := by
  induction records generalizing current next with
  | nil => rfl
  | cons bits rest ih =>
      rw [scan, ih, tagged, choose_pick]
      rfl

theorem callback_eval_raw (M : ℕ) (d : Data) (hd : Invariant M d) :
    ∃ n ≤ 100 * (M + (d.stacks 1).length + index d + 1), ∃ e : Data,
      Eval callback n d e ∧ Invariant M e ∧
      index e = index d + 1 ∧
      best e = pick (best d) ((d.stacks 1).length, index d) ∧
      e.stacks 1 = [] ∧ e.stacks 0 = d.stacks 0 ∧
      (∀ j : Fin 9, j.val < 3 → e.regs j = d.regs j) := by
  obtain ⟨hd3, hd4, hd5, hM, hi⟩ := hd
  let a := afterCopy d 2 3
  let b := afterCopy a 1 4
  have hcopy1 := copy_eval d 2 3 (by decide) (by decide) (by decide) hd5
  have hcopy2 := copy_eval a 1 4 (by decide) (by decide) (by decide)
    (by simpa [a, afterCopy, copyStacks] using hd5)
  obtain ⟨n, hn, e, he, hout, hr, hs, h3, h4⟩ := compare_eval b
  have hb3 : b.stacks 3 = d.stacks 2 := by simp [b, a, afterCopy, copyStacks, hd3]
  have hb4 : b.stacks 4 = d.stacks 1 := by simp [b, a, afterCopy, copyStacks, hd4]
  simp only [hb3, hb4] at hn hout h3 h4
  have hef (j : Fin 8) (hj3 : j ≠ 3) (hj4 : j ≠ 4) : e.stacks j = d.stacks j := by
    rw [hs j hj3 hj4]
    simp [b, a, afterCopy, copyStacks, hj3, hj4]
  have her (j : Fin 9) (hj : j.val < 3) : e.regs j = d.regs j := by
    rw [hr j (by omega)]
    have hj3 : j ≠ 3 := by intro h; subst j; omega
    have hj4 : j ≠ 4 := by intro h; subst j; omega
    simp [b, a, afterCopy, readRegs, hj3, hj4]
  have he0 := hef 0 (by decide) (by decide)
  have he1 := hef 1 (by decide) (by decide)
  have he2 := hef 2 (by decide) (by decide)
  have he5 : e.stacks 5 = [] := by rw [hef 5 (by decide) (by decide), hd5]
  have he6 := hef 6 (by decide) (by decide)
  have he7 := hef 7 (by decide) (by decide)
  let k := if (d.stacks 2).length ≤ (d.stacks 1).length then e else afterReplace e
  have hbranch : ∃ m ≤ 2 * (d.stacks 2).length + 7 * (d.stacks 1).length +
      2 * (d.stacks 7).length + 7 * (d.stacks 6).length + 17,
      Eval (.ite 8 (.base .skip) replaceBest) m e k := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length
    · refine ⟨1, by omega, ?_⟩
      simpa [k, hle] using
        (Eval.ite_true (by simpa [hle] using hout) (Eval.base (.skip e)))
    · refine ⟨2 * (e.stacks 2).length + 7 * (e.stacks 1).length +
        2 * (e.stacks 7).length + 7 * (e.stacks 6).length + 16 + 1, ?_, ?_⟩
      · simp [he1, he2, he6, he7]
      · simpa [k, hle] using
          (Eval.ite_false (by simpa [hle] using hout) (replaceBest_eval e he5))
  obtain ⟨m, hm, hbranch⟩ := hbranch
  have hk0 : k.stacks 0 = d.stacks 0 := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length <;>
      simp [k, hle, afterReplace, afterClear, afterCopy, clearStacks, copyStacks, he0]
  have hk1 : k.stacks 1 = d.stacks 1 := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length <;>
      simp [k, hle, afterReplace, afterClear, afterCopy, clearStacks, copyStacks, he1]
  have hk3 : k.stacks 3 = e.stacks 3 := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length <;>
      simp [k, hle, afterReplace, afterClear, afterCopy, clearStacks, copyStacks]
  have hk4 : k.stacks 4 = e.stacks 4 := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length <;>
      simp [k, hle, afterReplace, afterClear, afterCopy, clearStacks, copyStacks]
  have hk5 : k.stacks 5 = [] := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length <;>
      simp [k, hle, afterReplace, afterClear, afterCopy, clearStacks, copyStacks, he5]
  have hk6 : k.stacks 6 = d.stacks 6 := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length <;>
      simp [k, hle, afterReplace, afterClear, afterCopy, clearStacks, copyStacks, he6]
  have hkM : (k.stacks 2).length ≤ M := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length
    · simpa [k, hle, he2] using hM
    · simp [k, hle, afterReplace, afterClear, afterCopy, clearStacks, copyStacks, he1]
      omega
  have hki : (k.stacks 7).length ≤ (d.stacks 6).length := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length
    · simpa [k, hle, he7] using hi
    · simp [k, hle, afterReplace, afterClear, afterCopy, clearStacks, copyStacks, he6]
  have hkb : best k = pick (best d) ((d.stacks 1).length, index d) := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length <;>
      simp [k, best, pick, index, hle, afterReplace, afterClear, afterCopy,
        clearStacks, copyStacks, he1, he2, he6, he7]
  have hkr (j : Fin 9) (hj : j.val < 3) : k.regs j = d.regs j := by
    have hj3 : j ≠ 3 := by intro h; subst j; omega
    have hj4 : j ≠ 4 := by intro h; subst j; omega
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length <;>
      simp [k, hle, afterReplace, afterClear, afterCopy, readRegs, hj3, hj4, her j hj]
  have hclean := cleanup_eval k
  let total := (7 * (d.stacks 2).length + 5) +
    ((7 * (a.stacks 1).length + 5) +
      (n + (m + (2 * (k.stacks 1).length + 2 * (k.stacks 3).length +
        2 * (k.stacks 4).length + 11))))
  refine ⟨total, ?_, afterCleanup k, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hn' : n ≤ 4 * (d.stacks 2).length + 6 :=
      hn.trans (by gcongr; exact min_le_left _ _)
    simp only [total, a, afterCopy, copyStacks, Function.update_of_ne (show (1 : Fin 8) ≠ 3 by decide),
      hk1, hk3, hk4, index]
    omega
  · exact Eval.seq hcopy1 (Eval.seq hcopy2 (Eval.seq he (Eval.seq hbranch hclean)))
  · simp [Invariant, afterCleanup, afterIncrement, afterClear, clearStacks, hk5, hk6, hkM]
    omega
  · simp [index, afterCleanup, afterIncrement, afterClear, clearStacks, hk6]
  · simpa [best, afterCleanup, afterIncrement, afterClear, clearStacks] using hkb
  · simp [afterCleanup, afterIncrement, afterClear, clearStacks]
  · simpa [afterCleanup, afterIncrement, afterClear, clearStacks] using hk0
  · intro j hj
    have hj3 : j ≠ 3 := by intro h; subst j; omega
    have hj4 : j ≠ 4 := by intro h; subst j; omega
    simpa [afterCleanup, afterIncrement, afterClear, readRegs, hj3, hj4] using hkr j hj

theorem callback_eval (M : ℕ) (base : Data) (hd : Invariant M base)
    (bits tail : List Bool) :
    ∃ n ≤ 100 * (M + bits.length + index base + 1), ∃ e : Data,
      Invariant M e ∧ index e = index base + 1 ∧
      best e = pick (best base) (bits.length, index base) ∧
      Eval callback n
        (RecordPrograms.state ports base false true false tail bits.reverse)
        (RecordPrograms.state ports e false true false tail []) := by
  let d := RecordPrograms.state ports base false true false tail bits.reverse
  have hi : Invariant M d := by
    simpa [d, Invariant, RecordPrograms.state, ports] using hd
  obtain ⟨n, hn, e, he, hIe, hie, hbe, hp, hs, hr⟩ := callback_eval_raw M d hi
  have heq : RecordPrograms.state ports e false true false tail [] = e := by
    apply RecordPrograms.state_eq_self
    · simpa [d, RecordPrograms.state, ports] using hr 0 (by decide)
    · simpa [d, RecordPrograms.state, ports] using hr 1 (by decide)
    · simpa [d, RecordPrograms.state, ports] using hr 2 (by decide)
    · simpa [d, RecordPrograms.state, ports] using hs
    · exact hp
  refine ⟨n, ?_, e, hIe, ?_, ?_, ?_⟩
  · simpa [d, index, RecordPrograms.state, ports] using hn
  · simpa [d, index, RecordPrograms.state, ports] using hie
  · simpa [d, best, index, RecordPrograms.state, ports] using hbe
  · rwa [heq]

/-- A sum of actual per-record bounds, with the unary index increasing. -/
def scanBudget (M j : ℕ) : List (List Bool) → ℕ
  | [] => 1
  | bits :: rest => 107 * (M + bits.length + j + 1) + scanBudget M (j + 1) rest

theorem scanBudget_le (M j : ℕ) (records : List (List Bool)) :
    scanBudget M j records ≤ 107 *
      ((records.map List.length).sum + records.length * (M + j + records.length + 1)) + 1 := by
  induction records generalizing j with
  | nil => simp [scanBudget]
  | cons bits rest ih =>
      have h := ih (j + 1)
      simp only [scanBudget, List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

/-- The fixed parser/callback loop visits every record in order. -/
theorem loop_eval (M : ℕ) (records : List (List Bool)) (suffix : List Bool)
    (base : Data) (hd : Invariant M base) :
    ∃ n ≤ scanBudget M (index base) records, ∃ e : Data,
      Invariant M e ∧ index e = index base + records.length ∧
      best e = scan (best base) (index base) records ∧
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports base records suffix)
        (RecordPrograms.state ports e false true false suffix []) := by
  induction records generalizing base with
  | nil =>
      refine ⟨1, by simp [scanBudget], base, hd, by simp, rfl, ?_⟩
      exact Eval.while_false (by simp [RecordPrograms.afterTag])
  | cons bits rest ih =>
      let tail := Encoding.encodeList id rest ++ suffix
      obtain ⟨n, hn, middle, hm, hi, hb, hc⟩ := callback_eval M base hd bits tail
      have hr : Eval (RecordPrograms.reader ports) (6 * bits.length + 4)
          (RecordPrograms.afterTag ports base (bits :: rest) suffix)
          (RecordPrograms.state ports base false true false tail bits.reverse) := by
        simpa [RecordPrograms.afterTag, tail] using
          RecordPrograms.reader_eval ports base bits tail [] true true false
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports middle false true false tail [])
          (RecordPrograms.afterTag ports middle rest suffix) := by
        apply Eval.ite_false (by simp)
        exact RecordPrograms.pop_list_eval ports middle rest suffix false true
      obtain ⟨m, hmb, e, he, hei, heb, her⟩ := ih middle hm
      have hg : (RecordPrograms.afterTag ports base (bits :: rest) suffix).regs ports.tag = true := by
        simp [RecordPrograms.afterTag]
      refine ⟨(6 * bits.length + 4 + (n + 2)) + m + 1, ?_, e, he, ?_, ?_, ?_⟩
      · simp only [scanBudget]
        rw [hi] at hmb
        omega
      · rw [hei, hi, List.length_cons]
        omega
      · rw [heb, hb, hi]
        rfl
      · exact Eval.while_true hg (Eval.seq hr (Eval.seq hc hbranch)) her

theorem iterate_eval (M : ℕ) (records : List (List Bool)) (suffix : List Bool)
    (base : Data) (hd : Invariant M base) (v pr f : Bool) :
    ∃ n ≤ 2 + scanBudget M (index base) records, ∃ e : Data,
      Invariant M e ∧ index e = index base + records.length ∧
      best e = scan (best base) (index base) records ∧
      Eval (RecordPrograms.iterate ports callback) n
        (RecordPrograms.state ports base v pr f (Encoding.encodeList id records ++ suffix) [])
        (RecordPrograms.state ports e false true false suffix []) := by
  obtain ⟨n, hn, e, he, hi, hb, hr⟩ := loop_eval M records suffix base hd
  exact ⟨1 + (1 + n), by omega, e, he, hi, hb,
    Eval.seq (RecordPrograms.set_found_eval ports base v pr f false _ [])
      (Eval.seq (RecordPrograms.pop_list_eval ports base records suffix v pr) hr)⟩

abbrev initBest : Cmd 9 8 :=
  .seq (copy 1 2) (.seq (clear 1) increment)

def afterInitialize (d : Data) : Data :=
  afterIncrement (afterClear (afterCopy d 1 2) 1)

theorem initBest_eval (d : Data) (h5 : d.stacks 5 = []) :
    Eval initBest (9 * (d.stacks 1).length + 10) d (afterInitialize d) := by
  have h := Eval.seq (copy_eval d 1 2 (by decide) (by decide) (by decide) h5)
    (Eval.seq (clear_eval (afterCopy d 1 2) 1)
      (increment_eval (afterClear (afterCopy d 1 2) 1)))
  convert h using 1 <;>
    simp [ afterInitialize, afterCopy, copyStacks] ; omega

/-- The program is one fixed finite instruction table for every nonempty list. -/
abbrev command : Cmd 9 8 :=
  .seq (RecordPrograms.atom (.set ports.found false))
    (.seq (RecordPrograms.atom (.pop ports.source ports.tag ports.present))
      (.seq (RecordPrograms.reader ports)
        (.seq initBest (RecordPrograms.iterate ports callback))))

abbrev program : Program 9 8 (StructuredCalls.size command + 1) :=
  StructuredCalls.compiled command 0 7

def emptyData : Data := ⟨fun _ => false, fun _ => []⟩

def inputState (records : List (List Bool)) : Data :=
  RecordPrograms.state ports emptyData false false false
    (ProgramEncoding.encodeRecords records) []

/-- The score/index pair selected by the first-minimum rule. -/
def firstMinimum (first : List Bool) (rest : List (List Bool)) : ℕ × ℕ :=
  scan (first.length, 0) 1 rest

theorem command_eval (first : List Bool) (rest : List (List Bool)) :
    ∃ n ≤ 15 * first.length + 18 + scanBudget first.length 1 rest, ∃ e : Data,
      Eval command n (inputState (first :: rest)) e ∧
      (e.stacks 7).length = (firstMinimum first rest).2 := by
  let source := Encoding.encodeList id rest
  let d := RecordPrograms.state ports emptyData false true false source first.reverse
  let q := afterInitialize d
  have hq : Invariant first.length q := by
    simp [q, d, Invariant, afterInitialize, afterIncrement, afterClear, afterCopy,
      clearStacks, copyStacks, RecordPrograms.state, ports, emptyData]
  have hqi : index q = 1 := by
    simp [q, d, index, afterInitialize, afterIncrement, afterClear, afterCopy,
      clearStacks, copyStacks, RecordPrograms.state, ports, emptyData]
  have hqb : best q = (first.length, 0) := by
    simp [q, d, best, afterInitialize, afterIncrement, afterClear, afterCopy,
      clearStacks, copyStacks, RecordPrograms.state, ports, emptyData]
  have hqq : RecordPrograms.state ports q false true false source [] = q := by
    apply RecordPrograms.state_eq_self <;>
      simp [q, d, afterInitialize, afterIncrement, afterClear, afterCopy, readRegs,
        clearStacks, copyStacks, RecordPrograms.state, ports, emptyData]
  obtain ⟨m, hm, e, _, _, hb, hit⟩ :=
    iterate_eval first.length rest [] q hq false true false
  have hit' : Eval (RecordPrograms.iterate ports callback) m q
      (RecordPrograms.state ports e false true false [] []) := by
    simp only [List.append_nil] at hit
    change Eval _ m (RecordPrograms.state ports q false true false source []) _ at hit
    rwa [hqq] at hit
  have hinit : Eval initBest (9 * first.length + 10) d q := by
    simpa [q, d, RecordPrograms.state, ports] using initBest_eval d
      (by simp [d, RecordPrograms.state, ports, emptyData])
  have hreader : Eval (RecordPrograms.reader ports) (6 * first.length + 4)
      (RecordPrograms.afterTag ports emptyData (first :: rest) []) d := by
    simpa [RecordPrograms.afterTag, d, source] using
      RecordPrograms.reader_eval ports emptyData first source [] true true false
  have htotal := Eval.seq
    (RecordPrograms.set_found_eval ports emptyData false false false false
      (Encoding.encodeList id (first :: rest) ++ []) [])
    (Eval.seq (RecordPrograms.pop_list_eval ports emptyData (first :: rest) [] false false)
      (Eval.seq hreader (Eval.seq hinit hit')))
  refine ⟨1 + (1 + ((6 * first.length + 4) + ((9 * first.length + 10) + m))),
    ?_, RecordPrograms.state ports e false true false [] [], ?_, ?_⟩
  · rw [hqi] at hm
    omega
  · simpa [command, inputState, ProgramEncoding.encodeRecords] using htotal
  · rw [hqi, hqb] at hb
    have hp := congrArg Prod.snd hb
    simpa [best, firstMinimum, RecordPrograms.state, ports] using hp

theorem sourceBudget_le_quadratic (first : List Bool) (rest : List (List Bool)) :
    15 * first.length + 19 + scanBudget first.length 1 rest ≤
      500 * (first.length + (rest.map List.length).sum + rest.length + 1) ^ 2 := by
  have h := scanBudget_le first.length 1 rest
  have hsq := Nat.mul_self_le_mul_self
    (show rest.length ≤ first.length + (rest.map List.length).sum + rest.length + 1 by omega)
  nlinarith [Nat.zero_le ((rest.map List.length).sum * first.length),
    Nat.zero_le ((rest.map List.length).sum * rest.length),
    Nat.zero_le (first.length * first.length)]

/-- An actual halting trace, with polynomial cost in the prepared records. -/
theorem program_runsIn (first : List Bool) (rest : List (List Bool)) :
    ∃ e : Data,
      RunsIn program
        (500 * (first.length + (rest.map List.length).sum + rest.length + 1) ^ 2)
        ((inputState (first :: rest)).withPC (some program.entry))
        (e.withPC none) ∧
      (e.stacks 7).length = (firstMinimum first rest).2 := by
  obtain ⟨n, hn, e, he, hout⟩ := command_eval first rest
  refine ⟨e, ⟨n + 1, ?_, ?_⟩, hout⟩
  · exact (by omega : n + 1 ≤ 15 * first.length + 19 +
      scanBudget first.length 1 rest).trans (sourceBudget_le_quadratic first rest)
  · exact compiled_halt_trace he 0 7

theorem firstMinimum_eq_chooseMin (first : List Bool) (rest : List (List Bool)) :
    firstMinimum first rest =
      NaturalAssignment.chooseMinNat Prod.fst (first.length, 0) (tagged 1 rest) :=
  scan_eq_chooseMin _ _ _

/-- An indexed specification of the same earliest-minimum rule. -/
def indexChoice {A : Type*} (score : A → ℕ) (next : ℕ) (a : A) : List A → ℕ × A
  | [] => (next, a)
  | b :: bs =>
      let c := indexChoice score (next + 1) b bs
      if score a ≤ score c.2 then (next, a) else c

theorem indexChoice_value {A : Type*} (score : A → ℕ)
    (next : ℕ) (a : A) (tail : List A) :
    (indexChoice score next a tail).2 = NaturalAssignment.chooseMinNat score a tail := by
  induction tail generalizing next a with
  | nil => rfl
  | cons b bs ih =>
      simp only [indexChoice, NaturalAssignment.chooseMinNat, ih]
      split <;> simp_all only []

theorem indexChoice_lookup {A : Type*} (score : A → ℕ)
    (next : ℕ) (a : A) (tail : List A) :
    ∃ k < (a :: tail).length, (indexChoice score next a tail).1 = next + k ∧
      (a :: tail)[k]? = some (indexChoice score next a tail).2 := by
  induction tail generalizing next a with
  | nil => exact ⟨0, by simp, by simp [indexChoice], rfl⟩
  | cons b bs ih =>
      obtain ⟨k, hk, hi, hv⟩ := ih (next + 1) b
      by_cases h : score a ≤ score (indexChoice score (next + 1) b bs).2
      · exact ⟨0, by simp, by simp [indexChoice, h], by simp [indexChoice, h]⟩
      · refine ⟨k + 1, by simpa using Nat.succ_lt_succ hk, ?_, ?_⟩
        · simpa [indexChoice, h, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hi
        · simpa [indexChoice, h] using hv

theorem chooseTagged_indexChoice {A : Type*} (score : A → ℕ)
    (next : ℕ) (a : A) (tail : List A) :
    NaturalAssignment.chooseMinNat Prod.fst (score a, next)
      (tagged (next + 1) (tail.map (fun x => UnaryCompare.encode (score x)))) =
      (score (indexChoice score next a tail).2, (indexChoice score next a tail).1) := by
  induction tail generalizing next a with
  | nil => rfl
  | cons b bs ih =>
      have hlen (x : A) : (UnaryCompare.encode (score x)).length = score x := by
        simp [UnaryCompare.encode]
      simp only [List.map_cons, tagged, hlen, NaturalAssignment.chooseMinNat, ih, indexChoice]
      split <;> simp_all

/-- The unary program's output indexes the original candidate chosen by the
natural-number conditional-expectation algorithm. -/
theorem program_candidates {A : Type*} (score : A → ℕ) (a : A) (tail : List A) :
    ∃ e : Data, ∃ k < (a :: tail).length,
      RunsIn program
        (500 * (score a + (tail.map score).sum + tail.length + 1) ^ 2)
        ((inputState ((a :: tail).map (fun x => UnaryCompare.encode (score x)))).withPC
          (some program.entry)) (e.withPC none) ∧
      (e.stacks 7).length = k ∧
      (a :: tail)[k]? = some (NaturalAssignment.chooseMinNat score a tail) := by
  obtain ⟨e, he, hout⟩ := program_runsIn (UnaryCompare.encode (score a))
    (tail.map (fun x => UnaryCompare.encode (score x)))
  obtain ⟨k, hk, hi, hv⟩ := indexChoice_lookup score 0 a tail
  refine ⟨e, k, hk, ?_, ?_, ?_⟩
  · simpa [UnaryCompare.encode, List.map_map, Function.comp_def] using he
  · rw [firstMinimum_eq_chooseMin] at hout
    have hp := chooseTagged_indexChoice score 0 a tail
    simp only [UnaryCompare.encode_length] at hout
    change (e.stacks 7).length =
      (NaturalAssignment.chooseMinNat Prod.fst (score a, 0)
        (tagged (0 + 1) (tail.map (fun x => UnaryCompare.encode (score x))))).2 at hout
    rw [hp] at hout
    simpa [hi] using hout
  · simpa only [indexChoice_value] using hv

theorem program_runsIn_input_length (first : List Bool) (rest : List (List Bool)) :
    ∃ e : Data,
      RunsIn program (500 * ((ProgramEncoding.encodeRecords (first :: rest)).length + 1) ^ 2)
        ((inputState (first :: rest)).withPC (some program.entry)) (e.withPC none) ∧
      (e.stacks 7).length = (firstMinimum first rest).2 := by
  obtain ⟨e, ⟨n, hn, ht⟩, hout⟩ := program_runsIn first rest
  refine ⟨e, ⟨n, hn.trans ?_, ht⟩, hout⟩
  gcongr
  simp only [ProgramEncoding.encodeRecords_length, List.map_cons, List.sum_cons,
    List.length_cons]
  omega

end SubexponentialSAT.Subexp.MinimumProgram

end OAI.Algorithms
