import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScan
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

namespace OAI.Algorithms

/-! Paid joint-membership guard on actual type bytes. The four integer cache
words are arbitrary retained bytes; no finite-field numerator is invoked. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Guard

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.Subexp.MatrixWordEncoding SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

variable {r Q Δ : ℕ}

def guardInput (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ)
    (cache0 cache1 cache2 cache3 : List Bool) (regs : Fin 10 → Bool) : Data :=
  ⟨regs, fun j => if h : j.val < 37 then
    (Scan.scanInput i u y cache0 cache1 cache2 cache3
      (fun k => regs (k.castAdd 1))).stacks ⟨j.val,h⟩
    else if j = 37 then List.replicate t.val true else []⟩

theorem guardStage_eval (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (cache0 cache1 cache2 cache3 : List Bool) (regs : Fin 10 → Bool) :
    ∃ n ≤ guardStageCost r Q Δ i.val t.val, ∃ b : Data,
      Eval guardStage n (guardInput i t u y cache0 cache1 cache2 cache3 regs) b ∧
      b.stacks = (guardInput i t u y cache0 cache1 cache2 cache3 regs).stacks ∧
      b.regs 9 = decide (anchorValid i t u y) := by
  let base := guardInput i t u y cache0 cache1 cache2 cache3 regs
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
        simp +decide [ base, guardInput, Scan.scanInput,
          MatrixEntryProgram.input]
  obtain ⟨ne, hne, he⟩ := MatrixInputTypes.program_runsIn i u y lr
  rw [← hin] at he
  have te := liftCall_eval MatrixInputProgram.program (by decide) (by decide) base
    (MatrixInputTypes.output i u y lr) he
  have hwork : ∀ j : Fin 42, j.val < 9 → a1.stacks j = [] := by
    intro j hj
    fin_cases j <;>
      simp +decide [a1, install, MatrixInputTypes.output,
        MatrixInputProgram.outputState, MatrixInputProgram.inputState] at hj ⊢
  have hd : ∀ j, a1.stacks (MatrixAnchorReadProgram.target j) = [] := by
    intro j
    fin_cases j <;>
      simp +decide [a1, install, MatrixAnchorReadProgram.target, base, guardInput]
  have hs : ∀ j, a1.stacks (MatrixAnchorReadProgram.source j) = ReadPlan.encodeWord (ws j) := by
    intro j
    fin_cases j <;>
      simp +decide [a1, install, MatrixAnchorReadProgram.source, ws,
        MatrixInputTypes.output, MatrixInputProgram.outputState, MatrixInputProgram.inputState]
  have hi : (a1.stacks 37).length = t.val := by
    simp +decide [a1, install, base, guardInput]
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
        simp +decide [base, guardInput, Scan.scanInput, MatrixEntryProgram.input]
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
    simp only [MatrixAnchorGuardProgram.valid, hc38, hc39, hc40, hc41,
      ne_eq, MatrixAnchorReadProgram.colorWord_eq_iff, anchorValid]
    rfl
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


end SubexponentialSAT.SqrtLog.LayoutProgram.Guard

end OAI.Algorithms
