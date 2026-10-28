import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryExtract
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorGuardProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntrySemantics

namespace OAI.Algorithms

/-! Fixed control for the zero-extended joint entry on arbitrary universal
types. The unary position cursor is preserved on37. -/

namespace SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

open BitProgram StructuredCalls StackRoutines MatrixWordEncoding MulticolorTypes

abbrev Data := State 10 42
abbrev Code := Cmd 10 42

abbrev liftCall {k s l : ℕ} (p : Program k s l) (hk : k ≤ 10) (hs : s ≤ 42) : Code :=
  .call (ProgramLinking.liftProgram p (Fin.castLE hk) (Fin.castLE hs))

def readProgram := compiled MatrixAnchorReadProgram.readFour 17 38
def clear (src : Fin 42) : Code := .call (clearProgram src 0 1)
def copyZero : Code := .call (copyProgram 30 0 8 0 1)

def clearColors : Code :=
  .seq (clear 17) (.seq (clear 18) (.seq (clear 19) (.seq (clear 20)
    (.seq (clear 38) (.seq (clear 39) (.seq (clear 40) (clear 41)))))))

def guardStage : Code :=
  .seq (liftCall MatrixInputProgram.program (by decide) (by decide))
    (.seq (.call readProgram) (.seq (.call MatrixAnchorGuardProgram.program)
      clearColors))

def command : Code := .seq guardStage (.ite 9
  (liftCall MatrixEntryProgram.program (by decide) (by decide)) copyZero)

def program := compiled command 23 0

variable {r Q Δ : ℕ}

def typedInput (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (xs : List (ZMod p)) (regs : Fin 10 → Bool) : Data :=
  ⟨regs, fun j => if h : j.val < 37 then
    (MatrixEntryProgram.typedInput p i u y xs (fun k => regs (k.castAdd 1))).stacks ⟨j.val, h⟩
    else if j = 37 then List.replicate t.val true else []⟩

def output (base : Data) (regs : Fin 10 → Bool) (answer : List Bool) : Data :=
  ⟨regs, Function.update base.stacks 0 answer⟩

def project {k s : ℕ} (hk : k ≤ 10) (hs : s ≤ 42) (a : Data) : State k s :=
  ⟨fun j => a.regs (j.castLE hk), fun j => a.stacks (j.castLE hs)⟩

def install {k s : ℕ} (a : Data) (b : State k s) : Data :=
  ⟨fun j => if h : j.val < k then b.regs ⟨j.val, h⟩ else a.regs j,
    fun j => if h : j.val < s then b.stacks ⟨j.val, h⟩ else a.stacks j⟩

theorem castLE_injective {m n : ℕ} (h : m ≤ n) : Function.Injective (Fin.castLE h) := by
  intro i j hij
  exact Fin.ext (congrArg (fun k : Fin n => k.val) hij)

theorem embed_install {k s : ℕ} (hk : k ≤ 10) (hs : s ≤ 42) (a : Data) (b : State k s) :
    embedState (Fin.castLE hk) (Fin.castLE hs) a b = install a b := by
  apply embedState_eq_of_ports _ _ _ _ _ (castLE_injective hk) (castLE_injective hs)
  · intro j; simp [install, j.isLt]
  · intro j hj
    have hn : ¬ j.val < k := by
      intro h; exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
    simp [install, hn]
  · intro j; simp [install, j.isLt]
  · intro j hj
    have hn : ¬ j.val < s := by
      intro h; exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
    simp [install, hn]

theorem install_project {k s : ℕ} (hk : k ≤ 10) (hs : s ≤ 42) (a : Data) :
    install a (project hk hs a) = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    by_cases h : j.val < k <;> simp [ project, h]
  · funext j
    by_cases h : j.val < s <;> simp [ project, h]

theorem liftCall_eval {k s l : ℕ} (p : Program k s l) (hk : k ≤ 10) (hs : s ≤ 42)
    (a : Data) (b : State k s) {n : ℕ}
    (ht : Trace p n ((project hk hs a).withPC (some p.entry)) (b.withPC none)) :
    Eval (liftCall p hk hs) n a (install a b) := by
  have he := eval_call_lifted p (Fin.castLE hk) (Fin.castLE hs) a
    (castLE_injective hk) (castLE_injective hs) ht
  rw [embed_install, embed_install, install_project] at he
  exact he

def cleared (a : Data) (src : Fin 42) : Data :=
  ⟨readRegs a.regs 0 1 none, clearStacks src a.stacks⟩

theorem clear_eval (a : Data) (src : Fin 42) :
    Eval (clear src) (2 * (a.stacks src).length + 3) a (cleared a src) :=
  TupleProgram.clear_eval src (0 : Fin 10) 1 a

open BitProgram StructuredCalls StackRoutines

def colorsCleared (a : Data) : Data :=
  cleared (cleared (cleared (cleared (cleared (cleared (cleared (cleared a 17) 18) 19) 20)
    38) 39) 40) 41

def clearColorsCost (a : Data) : ℕ :=
  2 * ((a.stacks 17).length + (a.stacks 18).length + (a.stacks 19).length +
    (a.stacks 20).length + (a.stacks 38).length + (a.stacks 39).length +
    (a.stacks 40).length + (a.stacks 41).length) + 24

theorem clearColors_eval (a : Data) :
    Eval clearColors (clearColorsCost a) a (colorsCleared a) := by
  let a1 := cleared a 17
  let a2 := cleared a1 18
  let a3 := cleared a2 19
  let a4 := cleared a3 20
  let a5 := cleared a4 38
  let a6 := cleared a5 39
  let a7 := cleared a6 40
  have he := (clear_eval a 17).seq ((clear_eval a1 18).seq ((clear_eval a2 19).seq
    ((clear_eval a3 20).seq ((clear_eval a4 38).seq ((clear_eval a5 39).seq
      ((clear_eval a6 40).seq (clear_eval a7 41)))))))
  convert he using 1
  · rfl
  · simp +decide [clearColorsCost, a7, a6, a5, a4, a3, a2, a1, cleared, clearStacks]
    ring
  · rfl

theorem colorsCleared_reg9 (a : Data) : (colorsCleared a).regs 9 = a.regs 9 := by
  simp +decide [colorsCleared, cleared, readRegs]

theorem colorsCleared_stacks (a : Data) :
    (colorsCleared a).stacks = fun j =>
      if j ∈ ([17, 18, 19, 20, 38, 39, 40, 41] : List (Fin 42)) then [] else a.stacks j := by
  funext j
  fin_cases j <;> simp +decide [colorsCleared, cleared, clearStacks]

open BitProgram StructuredCalls StackRoutines MatrixWordEncoding MulticolorTypes


def guardStageCost (r Q Δ i t : ℕ) : ℕ :=
  (36 * CollisionProgram.typeWidth r Q Δ +
    4 * (i + 1) * (14 * (Q * r) + 17) + 203 * (Q * r) + 265) +
  (4 * (9 * (Q * r) + t * (14 * r + 17) + 30 * r + 43) + 1) +
  (81 * r + 107) + (8 * (Q * r) + 8 * r + 24)

theorem guardStage_eval (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (xs : List (ZMod p)) (regs : Fin 10 → Bool) :
    ∃ n ≤ guardStageCost r Q Δ i.val t.val, ∃ b : Data,
      Eval guardStage n (typedInput p i t u y xs regs) b ∧
      b.stacks = (typedInput p i t u y xs regs).stacks ∧
      b.regs 9 = decide (anchorValid i t u y) := by
  let base := typedInput p i t u y xs regs
  let lr : Fin 8 → Bool := fun j => regs (j.castLE (by decide : 8 ≤ 10))
  let a1 := install base (MatrixInputTypes.output i u y lr)
  let ws : Fin 4 → Word r Q := ![u.head, u.slot i, y.head, y.slot i]
  let colors := fun j => MatrixAnchorReadProgram.colorWord (ws j t)
  let a2 := MatrixAnchorReadProgram.fourReadResult a1 colors
  have hin : project (by decide : 8 ≤ 10) (by decide : 29 ≤ 42) base =
      MatrixInputTypes.input i u y lr := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;>
        simp +decide [ base, typedInput, MatrixEntryProgram.typedInput,
          MatrixEntryProgram.input]
  obtain ⟨ne, hne, he⟩ := MatrixInputTypes.program_runsIn i u y lr
  rw [← hin] at he
  have te := liftCall_eval MatrixInputProgram.program (by decide) (by decide) base
    (MatrixInputTypes.output i u y lr) he
  have hwork : ∀ j : Fin 42, j.val < 9 → a1.stacks j = [] := by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
        j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
    rcases hjcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp +decide [a1, install, MatrixInputTypes.output,
        MatrixInputProgram.outputState, MatrixInputProgram.inputState]
  have hd : ∀ j, a1.stacks (MatrixAnchorReadProgram.target j) = [] := by
    intro j
    fin_cases j <;>
      simp +decide [a1, install, MatrixAnchorReadProgram.target, base, typedInput]
  have hs : ∀ j, a1.stacks (MatrixAnchorReadProgram.source j) = ReadPlan.encodeWord (ws j) := by
    intro j
    fin_cases j <;>
      simp +decide [a1, install, MatrixAnchorReadProgram.source, ws,
        MatrixInputTypes.output, MatrixInputProgram.outputState, MatrixInputProgram.inputState]
  have hi : (a1.stacks 37).length = t.val := by
    simp +decide [a1, install, base, typedInput]
  have hw : (a1.stacks 21).length = r := by
    simp +decide [a1, install, MatrixInputTypes.output,
      MatrixInputProgram.outputState, MatrixInputProgram.inputState]
  have hr := MatrixAnchorReadProgram.readFour_typed a1 ws t hwork hd hs hi hw
  have tr : Eval (.call readProgram)
      (4 * (9 * (Q * r) + t.val * (14 * r + 17) + 30 * r + 43) + 1) a1 a2 :=
    .call _ (compiled_halt_trace hr 17 38)
  have hb0 : a2.stacks 0 = [] := by
    simpa +decide [a2, MatrixAnchorReadProgram.fourReadResult,
      MatrixAnchorReadProgram.readOneResult, MatrixAnchorReadProgram.target] using hwork 0 (by decide)
  have hb1 : a2.stacks 1 = [] := by
    simpa +decide [a2, MatrixAnchorReadProgram.fourReadResult,
      MatrixAnchorReadProgram.readOneResult, MatrixAnchorReadProgram.target] using hwork 1 (by decide)
  have hb11 : a2.stacks 11 = [] := by
    simp +decide [a2, MatrixAnchorReadProgram.fourReadResult, MatrixAnchorReadProgram.readOneResult,
      MatrixAnchorReadProgram.target, a1, install, MatrixInputTypes.output,
      MatrixInputProgram.outputState, MatrixInputProgram.inputState]
  have hb12 : a2.stacks 12 = [] := by
    simp +decide [a2, MatrixAnchorReadProgram.fourReadResult, MatrixAnchorReadProgram.readOneResult,
      MatrixAnchorReadProgram.target, a1, install, MatrixInputTypes.output,
      MatrixInputProgram.outputState, MatrixInputProgram.inputState]
  obtain ⟨a3, ⟨ng, hng, hg⟩, hs3, hf3⟩ := MatrixAnchorGuardProgram.program_runsIn a2 hb0 hb1 hb11 hb12
  have tg : Eval (.call MatrixAnchorGuardProgram.program) ng a2 a3 := .call _ hg
  let a4 := colorsCleared a3
  have tc := clearColors_eval a3
  have hbaseLow (j : Fin 42) (hj : j.val < 29) :
      base.stacks j = (MatrixInputTypes.input i u y lr).stacks ⟨j.val, hj⟩ := by
    have h := congrFun (congrArg StructuredProgram.State.stacks hin) ⟨j.val, hj⟩
    have heq : Fin.castLE (by decide : 29 ≤ 42) ⟨j.val, hj⟩ = j := Fin.ext rfl
    simpa only [project, heq] using h
  have ha1 (j : Fin 42) :
      (if j ∈ ([17, 18, 19, 20, 38, 39, 40, 41] : List (Fin 42)) then []
        else a1.stacks j) = base.stacks j := by
    by_cases hmem : j ∈ ([17, 18, 19, 20, 38, 39, 40, 41] : List (Fin 42))
    · simp only [ite_eq_left hmem]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h | h | h | h | h <;> subst j <;>
        simp +decide [base, typedInput, MatrixEntryProgram.typedInput,
          MatrixEntryProgram.input]
    · simp only [ite_eq_right hmem]
      by_cases hj : j.val < 29
      · have h17 : j.val ≠ 17 := by
          intro h
          apply hmem
          have : j = (17 : Fin 42) := Fin.ext h
          subst j
          simp
        have h18 : j.val ≠ 18 := by
          intro h
          apply hmem
          have : j = (18 : Fin 42) := Fin.ext h
          subst j
          simp
        have h19 : j.val ≠ 19 := by
          intro h
          apply hmem
          have : j = (19 : Fin 42) := Fin.ext h
          subst j
          simp
        have h20 : j.val ≠ 20 := by
          intro h
          apply hmem
          have : j = (20 : Fin 42) := Fin.ext h
          subst j
          simp
        rw [hbaseLow j hj]
        simp +decide [a1, install, hj, MatrixInputTypes.output, MatrixInputTypes.input,
          MatrixInputProgram.outputState, MatrixInputProgram.inputState, Fin.ext_iff,
          h17, h18, h19, h20]
      · simp +decide [a1, install, hj]
  have hfinal : a4.stacks = base.stacks := by
    rw [show a4 = colorsCleared a3 from rfl, colorsCleared_stacks, hs3]
    funext j
    by_cases hmem : j ∈ ([17, 18, 19, 20, 38, 39, 40, 41] : List (Fin 42))
    · simpa only [ite_eq_left hmem] using ha1 j
    · have h38 : j ≠ 38 := by intro h; subst j; exact hmem (by simp)
      have h39 : j ≠ 39 := by intro h; subst j; exact hmem (by simp)
      have h40 : j ≠ 40 := by intro h; subst j; exact hmem (by simp)
      have h41 : j ≠ 41 := by intro h; subst j; exact hmem (by simp)
      simpa +decide [a2, MatrixAnchorReadProgram.fourReadResult,
        MatrixAnchorReadProgram.readOneResult, MatrixAnchorReadProgram.target,
        hmem, h38, h39, h40, h41] using ha1 j
  have hc38 : a2.stacks 38 = MatrixAnchorReadProgram.colorWord (u.head t) := rfl
  have hc39 : a2.stacks 39 = MatrixAnchorReadProgram.colorWord (u.slot i t) := rfl
  have hc40 : a2.stacks 40 = MatrixAnchorReadProgram.colorWord (y.head t) := rfl
  have hc41 : a2.stacks 41 = MatrixAnchorReadProgram.colorWord (y.slot i t) := rfl
  have hflag : a4.regs 9 = decide (anchorValid i t u y) := by
    rw [show a4 = colorsCleared a3 from rfl, colorsCleared_reg9, hf3]
    simp only [MatrixAnchorGuardProgram.valid, hc38, hc39, hc40, hc41, anchorValid,
      MatrixAnchorReadProgram.colorWord_eq_iff]
    by_cases h₀ : u.head t = y.head t <;>
      by_cases h₁ : u.slot i t = y.head t <;>
      by_cases h₂ : y.slot i t = y.head t <;> simp [h₀, h₁, h₂]
  have hcostg : MatrixAnchorGuardProgram.cost a2 + 1 = 81 * r + 107 := by
    simp only [MatrixAnchorGuardProgram.cost, hc38, hc39, hc40, hc41,
      MatrixAnchorReadProgram.colorWord_length]
    ring
  have hcostc : clearColorsCost a3 = 8 * (Q * r) + 8 * r + 24 := by
    simp only [clearColorsCost, hs3, hc38, hc39, hc40, hc41]
    simp +decide [a2,
      MatrixAnchorReadProgram.fourReadResult, MatrixAnchorReadProgram.readOneResult,
      MatrixAnchorReadProgram.target, colors, a1, install, MatrixInputTypes.output,
      MatrixInputProgram.outputState, ReadPlan.wordWidth]
    ring
  refine ⟨ne + ((4 * (9 * (Q * r) + t.val * (14 * r + 17) + 30 * r + 43) + 1) +
    (ng + clearColorsCost a3)), ?_, a4, te.seq (tr.seq (tg.seq tc)), hfinal, hflag⟩
  rw [hcostg] at hng
  rw [hcostc]
  dsimp [guardStageCost]
  omega

end SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

end OAI.Algorithms
