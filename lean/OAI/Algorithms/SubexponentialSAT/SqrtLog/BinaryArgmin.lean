import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularPrograms
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-!
# A binary-score minimum update implemented by finite bit programs

The score is a little-endian bit word. Comparisons inspect its numeric value,
not its length. Candidate payloads may themselves be binary indices or encoded
rows. Ports 0/1 hold the incoming payload/score, 2/3 the incumbent, 4--7 are
scratch, and 8 is an untouched caller queue. Every copy and comparison below
has a measured trace of a fixed finite instruction table.
-/

namespace SubexponentialSAT.SqrtLog.BinaryArgmin

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 8 9

structure Entry where
  payload : List Bool
  score : List Bool
  deriving DecidableEq

def value (a : Entry) : ℕ := BinaryArithmetic.toNat a.score

def pick (best next : Entry) : Entry := if value next < value best then next else best

def empty : Entry := ⟨[], []⟩

def store (next best : Entry) (queue : List Bool) : Fin 9 → List Bool :=
  ![next.payload, next.score, best.payload, best.score, [], [], [], [], queue]

def data (regs : Fin 8 → Bool) (next best : Entry) (queue : List Bool) : Data :=
  ⟨regs, store next best queue⟩

abbrev atom (a : StructuredProgram.Atom 8 9) : Cmd 8 9 := .base (.atom a)
abbrev clear (dst : Fin 9) : Cmd 8 9 := .call (clearProgram dst 1 2)
abbrev copy (src dst : Fin 9) : Cmd 8 9 := .call (copyProgram src dst 7 1 2)

def afterClear (d : Data) (dst : Fin 9) : Data :=
  ⟨readRegs d.regs 1 2 none, clearStacks dst d.stacks⟩
def afterCopy (d : Data) (src dst : Fin 9) : Data :=
  ⟨readRegs d.regs 1 2 none, copyStacks src dst d.stacks⟩
def reset (d : Data) : Data := ⟨Function.update d.regs 0 false, d.stacks⟩

theorem clear_eval (d : Data) (dst : Fin 9) :
    Eval (clear dst) (2 * (d.stacks dst).length + 3) d (afterClear d dst) :=
  .call _ (ListRegisterProgram.clear_run dst 1 2 d.regs d.stacks)

theorem copy_eval (d : Data) (src dst : Fin 9)
    (hsd : src ≠ dst) (hs : src ≠ 7) (hd : (7 : Fin 9) ≠ dst)
    (htmp : d.stacks 7 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (afterCopy d src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 7 1 2 hsd hs hd
    (by decide) d.regs d.stacks htmp)

theorem reset_eval (d : Data) : Eval (atom (.set 0 false)) 1 d (reset d) := by
  exact Eval.base (StructuredProgram.Eval.atom (.set 0 false) d)

def compareStacks : Fin 3 → Fin 9 := ![4, 5, 6]

theorem compareStacks_injective : Function.Injective compareStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [compareStacks]

abbrev comparator : Program 8 9 13 :=
  ProgramLinking.liftProgram ModularPrograms.subtractProgram id compareStacks

private theorem state_ext {a b : Data}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

private theorem embed_input (d : Data) (h6 : d.stacks 6 = []) :
    embedState id compareStacks d
      ⟨d.regs, ModularPrograms.operandStacks (d.stacks 4) (d.stacks 5) []⟩ = d := by
  apply state_ext
  · funext j
    exact embedState_register _ _ _ _ Function.injective_id j
  · funext j
    by_cases h : ∃ i, compareStacks i = j
    · obtain ⟨i, rfl⟩ := h
      rw [embedState_stack _ _ _ _ compareStacks_injective]
      fin_cases i <;> simp [compareStacks, ModularPrograms.operandStacks, h6]
    · exact embedState_stack_frame _ _ _ _ j h

/-- Destructive binary comparison; only scratch stacks 4, 5, 6 change. -/
theorem compare_eval (d : Data) (h0 : d.regs 0 = false)
    (h6 : d.stacks 6 = []) (hlen : (d.stacks 4).length = (d.stacks 5).length) :
    ∃ e : Data,
      Eval (.call comparator) (12 * (d.stacks 4).length + 3) d e ∧
      (e.regs 0 = true ↔ BinaryArithmetic.toNat (d.stacks 4) <
        BinaryArithmetic.toNat (d.stacks 5)) ∧
      e.stacks 4 = [] ∧ e.stacks 5 = [] ∧
      (e.stacks 6).length = (d.stacks 4).length ∧
      (∀ j : Fin 9, j ≠ 4 → j ≠ 5 → j ≠ 6 → e.stacks j = d.stacks j) := by
  obtain ⟨regs, ht, hb⟩ := ModularPrograms.subtract_comparison d.regs
    (d.stacks 4) (d.stacks 5) h0 hlen
  let out : State 8 3 := ⟨regs, ModularPrograms.operandStacks [] []
    (ModularArithmetic.subCarry false (d.stacks 4) (d.stacks 5)).1.reverse⟩
  let e := embedState id compareStacks d out
  change Trace ModularPrograms.subtractProgram _
    ((⟨d.regs, ModularPrograms.operandStacks (d.stacks 4) (d.stacks 5) []⟩ :
      State 8 3).withPC (some ModularPrograms.subtractProgram.entry))
    (out.withPC none) at ht
  have he := eval_call_lifted ModularPrograms.subtractProgram id compareStacks d
    Function.injective_id compareStacks_injective ht
  rw [embed_input d h6] at he
  refine ⟨e, he, ?_, ?_, ?_, ?_, ?_⟩
  · change (embedState id compareStacks d out).regs (id 0) = true ↔ _
    rw [embedState_register _ _ _ _ Function.injective_id]
    exact hb
  · exact embedState_stack _ _ _ _ compareStacks_injective 0
  · exact embedState_stack _ _ _ _ compareStacks_injective 1
  · change ((embedState id compareStacks d out).stacks (compareStacks 2)).length = _
    rw [embedState_stack _ _ _ _ compareStacks_injective]
    simpa [out] using ModularArithmetic.subCarry_length false
      (d.stacks 4) (d.stacks 5) hlen
  · intro j h4 h5 h6
    apply embedState_stack_frame
    rintro ⟨i, hi⟩
    fin_cases i <;> simp_all [compareStacks]

abbrev replace : Cmd 8 9 :=
  .seq (clear 2) (.seq (copy 0 2) (.seq (clear 3) (copy 1 3)))

def afterReplace (d : Data) : Data :=
  afterCopy (afterClear (afterCopy (afterClear d 2) 0 2) 3) 1 3

theorem replace_eval (d : Data) (htmp : d.stacks 7 = []) :
    Eval replace (2 * (d.stacks 2).length + 7 * (d.stacks 0).length +
      2 * (d.stacks 3).length + 7 * (d.stacks 1).length + 16) d (afterReplace d) := by
  have h1 := clear_eval d 2
  have h2 := copy_eval (afterClear d 2) 0 2 (by decide) (by decide) (by decide)
    (by simpa [afterClear, clearStacks] using htmp)
  have h3 := clear_eval (afterCopy (afterClear d 2) 0 2) 3
  have h4 := copy_eval (afterClear (afterCopy (afterClear d 2) 0 2) 3) 1 3
    (by decide) (by decide) (by decide)
    (by simpa [afterClear, afterCopy, clearStacks, copyStacks] using htmp)
  convert Eval.seq h1 (Eval.seq h2 (Eval.seq h3 h4)) using 1 <;>
    simp [ afterReplace, afterClear, afterCopy, clearStacks, copyStacks] ; omega

abbrev cleanup : Cmd 8 9 := .seq (clear 0) (.seq (clear 1) (clear 6))
def afterCleanup (d : Data) : Data := afterClear (afterClear (afterClear d 0) 1) 6

theorem cleanup_eval (d : Data) :
    Eval cleanup (2 * (d.stacks 0).length + 2 * (d.stacks 1).length +
      2 * (d.stacks 6).length + 9) d (afterCleanup d) := by
  convert Eval.seq (clear_eval d 0) (Eval.seq (clear_eval (afterClear d 0) 1)
    (clear_eval (afterClear (afterClear d 0) 1) 6)) using 1 <;>
    simp [ afterCleanup, afterClear, clearStacks] ; omega

abbrev update : Cmd 8 9 :=
  .seq (copy 1 4) (.seq (copy 3 5) (.seq (atom (.set 0 false))
    (.seq (.call comparator) (.seq (.ite 0 replace (.base .skip)) cleanup))))

/-- One strict-improvement update. The bound depends on bit lengths, never on
the numeric score. The queue and the first incumbent on equal scores survive. -/
theorem update_eval (B C : ℕ) (next best : Entry) (queue : List Bool)
    (regs : Fin 8 → Bool) (hn : next.score.length = B)
    (hb : best.score.length = B) (hcn : next.payload.length ≤ C)
    (hcb : best.payload.length ≤ C) :
    ∃ n ≤ 100 * (B + C + 1), ∃ regs',
      Eval update n (data regs next best queue)
        (data regs' empty (pick best next) queue) := by
  let d := data regs next best queue
  let a := afterCopy d 1 4
  let b := afterCopy a 3 5
  let c := reset b
  have hcopy1 := copy_eval d 1 4 (by decide) (by decide) (by decide) (by rfl)
  have hcopy2 := copy_eval a 3 5 (by decide) (by decide) (by decide) (by rfl)
  have hc4 : c.stacks 4 = next.score := by simp [c, b, a, d, reset, afterCopy, copyStacks, data, store]
  have hc5 : c.stacks 5 = best.score := by simp [c, b, a, d, reset, afterCopy, copyStacks, data, store]
  obtain ⟨e, he, hlt, he4, he5, he6, hef⟩ := compare_eval c (by simp [c, reset])
    (by rfl) (by rw [hc4, hc5, hn, hb])
  rw [hc4, hc5] at hlt
  rw [hc4, hn] at he6
  have he0 : e.stacks 0 = next.payload := by
    rw [hef 0 (by decide) (by decide) (by decide)]; rfl
  have he1 : e.stacks 1 = next.score := by
    rw [hef 1 (by decide) (by decide) (by decide)]; rfl
  have he2 : e.stacks 2 = best.payload := by
    rw [hef 2 (by decide) (by decide) (by decide)]; rfl
  have he3 : e.stacks 3 = best.score := by
    rw [hef 3 (by decide) (by decide) (by decide)]; rfl
  have he7 : e.stacks 7 = [] := by
    rw [hef 7 (by decide) (by decide) (by decide)]; rfl
  have he8 : e.stacks 8 = queue := by
    rw [hef 8 (by decide) (by decide) (by decide)]; rfl
  let k := if value next < value best then afterReplace e else e
  have hbranch : ∃ m ≤ 9 * C + 9 * B + 17,
      Eval (.ite 0 replace (.base .skip)) m e k := by
    by_cases h : value next < value best
    · refine ⟨2 * (e.stacks 2).length + 7 * (e.stacks 0).length +
        2 * (e.stacks 3).length + 7 * (e.stacks 1).length + 16 + 1, ?_, ?_⟩
      · rw [he2, he0, he3, he1, hn, hb]; omega
      · simpa [k, h] using Eval.ite_true (hlt.mpr h) (replace_eval e he7)
    · refine ⟨1, by omega, ?_⟩
      have hf : e.regs 0 = false := by
        cases hv : e.regs 0 <;> simp_all [value]
      simpa [k, h] using Eval.ite_false hf (Eval.base (.skip e))
  obtain ⟨m, hm, hbranch⟩ := hbranch
  have hk0 : k.stacks 0 = next.payload := by
    dsimp only [k]
    split_ifs <;> simp [afterReplace, afterCopy, afterClear, copyStacks, clearStacks, he0]
  have hk1 : k.stacks 1 = next.score := by
    dsimp only [k]
    split_ifs <;> simp [afterReplace, afterCopy, afterClear, copyStacks, clearStacks, he1]
  have hk6 : (k.stacks 6).length = B := by
    dsimp only [k]
    split_ifs <;> simpa [afterReplace, afterCopy, afterClear, copyStacks, clearStacks] using he6
  have hfinal : afterCleanup k =
      data (afterCleanup k).regs empty (pick best next) queue := by
    apply state_ext
    · rfl
    · funext j
      by_cases h : value next < value best <;> fin_cases j <;>
        simp [afterCleanup, k, pick, h, afterReplace, afterClear, afterCopy,
          clearStacks, copyStacks, data, store, empty, he0, he1, he2, he3, he4, he5, he7, he8]
  let total := (7 * (d.stacks 1).length + 5) +
    ((7 * (a.stacks 3).length + 5) +
      (1 + ((12 * (c.stacks 4).length + 3) +
        (m + (2 * (k.stacks 0).length + 2 * (k.stacks 1).length +
          2 * (k.stacks 6).length + 9)))))
  refine ⟨total, ?_, (afterCleanup k).regs, ?_⟩
  · simp only [total, hk0, hk1, hk6, hc4]
    have hd1 : d.stacks 1 = next.score := rfl
    have ha3 : a.stacks 3 = best.score := rfl
    rw [hd1, ha3, hn, hb]
    omega
  · rw [← hfinal]
    exact Eval.seq hcopy1 (Eval.seq hcopy2 (Eval.seq (reset_eval b)
      (Eval.seq he (Eval.seq hbranch (cleanup_eval k)))))

end SubexponentialSAT.SqrtLog.BinaryArgmin

end OAI.Algorithms
