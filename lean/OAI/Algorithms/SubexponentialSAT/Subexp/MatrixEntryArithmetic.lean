import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryPrepare
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntrySelect

namespace OAI.Algorithms

/-! Actual zero padding, repeated adjacent additions, coefficient selection,
sign application, and workspace cleanup for the fixed joint-entry program. -/

namespace SubexponentialSAT.Subexp.MatrixEntryProgram

open BitProgram StructuredCalls StackRoutines MatrixWordEncoding

def paddedCoefficients {p : ℕ} (xs : List (ZMod p)) (Q : ℕ) : List (ZMod p) :=
  xs ++ List.replicate (Q + 1) 0

def coefficientResult (base : Data) (regs : Fin 9 → Bool) (p : ℕ)
    [Fact p.Prime] (ys : List (ZMod p)) (A B : ℕ) : Data :=
  install (prepared base regs A B)
    (MatrixPascalProgram.resting p (fun j => regs (lowRegisters j)) ys [])

def coefficientStageCost (p R Q B : ℕ) : ℕ :=
  MatrixPaddingProgram.cost (R * (2 * width p + 1)) (width p) (Q + 1) + 1 +
    (7 * B + 5) +
    (B * (MatrixPascalProgram.passBudget (R + (Q + 1)) (width p) + 2) + 3)

theorem coefficientStage_eval (p : ℕ) [Fact p.Prime]
    (base : Data) (regs : Fin 9 → Bool) (xs : List (ZMod p)) (A B Q : ℕ)
    (hmod : base.stacks 29 = modulus p) (hzero : base.stacks 30 = word p 0)
    (hxs : base.stacks 31 = CoefficientPascalProgram.valueWords p xs)
    (hR : base.stacks 32 = List.replicate xs.length true)
    (hQ : base.stacks 22 = List.replicate Q true) :
    ∃ n ≤ coefficientStageCost p xs.length Q B, ∃ out,
      Eval coefficientStage n (prepared base regs A B)
        (coefficientResult base out p
          (MatrixPascalProgram.repeated p B (paddedCoefficients xs Q)) A B) := by
  let zs := paddedCoefficients xs Q
  let a := prepared base regs A B
  obtain ⟨rp, np, hnp, hp⟩ := MatrixPaddingProgram.program_runsIn
    (fun j => regs (lowRegisters j)) (xs.map (word p)) (word p 0) (modulus p)
    (List.replicate xs.length true) (Q + 1)
  have hin : project (by decide : 18 ≤ 37) a =
      MatrixPaddingProgram.state (fun j => regs (lowRegisters j))
        (MatrixProgramSupport.words (xs.map (word p))) (word p 0) (modulus p)
        (List.replicate (Q + 1) true) (List.replicate xs.length true) := by
    rw [show a = prepared base regs A B from rfl, prepared_projection]
    simp [hmod, hzero, hxs, hR, hQ, CoefficientPascalProgram.valueWords,
      List.replicate_succ]
  have htemplate : List.replicate (Q + 1) true ++ List.replicate xs.length true =
      List.replicate (xs.length + (Q + 1)) true := by
    rw [← List.replicate_add]
    congr 1
    omega
  have hout : MatrixPaddingProgram.state rp
      (MatrixProgramSupport.words (xs.map (word p) ++ List.replicate (Q + 1) (word p 0)))
      (word p 0) (modulus p) []
      (List.replicate (Q + 1) true ++ List.replicate xs.length true) =
        MatrixPascalProgram.resting p rp zs [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;>
        simp [
 MatrixPascalProgram.extend,
 MatrixScalarProgram.scalarStacks, zs, paddedCoefficients,
          CoefficientPascalProgram.valueWords, List.map_append, List.map_replicate,
          htemplate]
  rw [← hin, hout] at hp
  have tp := callLow_eval MatrixPaddingProgram.program (by decide) a
    (MatrixPascalProgram.resting p rp zs []) hp
  let a1 := install a (MatrixPascalProgram.resting p rp zs [])
  let a2 := copied a1 36 16
  have tc := copy_eval a1 36 16 (by decide) (by decide) (by decide)
    (by simp +decide [a1, install, MatrixPascalProgram.resting, MatrixPascalProgram.stage,
      MatrixPascalProgram.frame, MatrixPascalProgram.extend,
      MatrixScalarProgram.scalarStacks])
  have hb : (a1.stacks 36).length = B := by
    simp +decide [a1, a, install, prepared]
  have hin2 : project (by decide : 18 ≤ 37) a2 =
      MatrixPascalProgram.resting p (fun j => a2.regs (lowRegisters j)) zs
        (List.replicate B true) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;>
        simp +decide [ a2, a1, a, copied, copyStacks, install, prepared,
          MatrixPascalProgram.resting, MatrixPascalProgram.stage, MatrixPascalProgram.frame,
          MatrixPascalProgram.extend, MatrixScalarProgram.scalarStacks]
  obtain ⟨rf, nf, hnf, hf⟩ := MatrixPascalProgram.program_runsIn p B zs
    (fun j => a2.regs (lowRegisters j))
  rw [← hin2] at hf
  have tf := callLow_eval MatrixPascalProgram.program (by decide) a2
    (MatrixPascalProgram.resting p rf (MatrixPascalProgram.repeated p B zs) []) hf
  let a3 := install a2 (MatrixPascalProgram.resting p rf (MatrixPascalProgram.repeated p B zs) [])
  have hend : a3 = coefficientResult base a3.regs p (MatrixPascalProgram.repeated p B zs) A B := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      by_cases hj : j.val < 8 <;>
        simp [a3, install, prepared, MatrixPascalProgram.resting,
          MatrixPascalProgram.stage, MatrixPascalProgram.frame,
          lowRegisters, hj]
    · funext j
      by_cases hj : j.val < 18
      · simp [a3, install, hj, MatrixPascalProgram.resting,
          MatrixPascalProgram.stage, MatrixPascalProgram.frame]
      · have h16 : j ≠ 16 := by intro h; subst j; exact hj (by decide)
        simp [a3, a2, a1, a, install, copied, copyStacks, hj, h16,
          prepared]
  have he := tp.seq (tc.seq (tf.seq (Eval.base (StructuredProgram.Eval.skip a3))))
  rw [hend] at he
  refine ⟨np + ((7 * B + 5) + (nf + 0)), ?_, a3.regs, ?_⟩
  · have hz : zs.length = xs.length + (Q + 1) := by simp [zs, paddedCoefficients]
    have hc : (MatrixProgramSupport.words (xs.map (word p))).length =
        xs.length * (2 * width p + 1) := CoefficientPascalProgram.valueWords_length p xs
    rw [hc, word_length] at hnp
    rw [hz] at hnf
    dsimp [coefficientStageCost]
    omega
  · simpa only [coefficientStage, series, hb] using he

open BitProgram StructuredCalls StackRoutines MatrixWordEncoding

def frameWidthWord (p : ℕ) [Fact p.Prime] : List Bool :=
  true :: (word p 0 ++ word p 0)

def finished (base : Data) (regs : Fin 9 → Bool) (p : ℕ) [Fact p.Prime]
    (ys : List (ZMod p)) (A B : ℕ) : Data :=
  ⟨regs, Function.update (Function.update (Function.update
    (coefficientResult base regs p ys A B).stacks 10 (frameWidthWord p)) 34 [])
      0 (word p ((-1 : ZMod p)^A * ys.getD A 0))⟩

def finishEntryCost (p A : ℕ) : ℕ :=
  2 * (7 * width p + 5) + 2 + (7 * A + 5) +
    (MatrixWordSelectProgram.budget A (width p) + 1) +
    (6073 * (width p + 1)^2 + 3 * A + 7)

theorem finishEntry_eval (p : ℕ) [Fact p.Prime] (base : Data)
    (regs : Fin 9 → Bool) (ys : List (ZMod p)) (A B : ℕ)
    (hA : A < ys.length) (hzero : base.stacks 30 = word p 0) :
    ∃ n ≤ finishEntryCost p A, ∃ out,
      Eval finishEntry n (coefficientResult base regs p ys A B)
        (finished base out p ys A B) := by
  let a := coefficientResult base regs p ys A B
  let a1 := copied a 30 10
  let a2 := copied a1 30 10
  let a3 := pushed a2 10
  let a4 := copied a3 35 15
  have ha10 : a.stacks 10 = [] := rfl
  have ha30 : a.stacks 30 = word p 0 := by
    simp +decide [a, coefficientResult, install, prepared, hzero]
  have t0 := copy_eval a 30 10 (by decide) (by decide) (by decide)
    (by simp +decide [a, coefficientResult, install, MatrixPascalProgram.resting,
      MatrixPascalProgram.stage, MatrixPascalProgram.frame, MatrixPascalProgram.extend,
 MatrixScalarProgram.scalarStacks])
  have t1 := copy_eval a1 30 10 (by decide) (by decide) (by decide)
    (by simp +decide [a1, a, copied, copyStacks, coefficientResult, install,
      MatrixPascalProgram.resting, MatrixPascalProgram.stage, MatrixPascalProgram.frame,
      MatrixPascalProgram.extend, MatrixScalarProgram.scalarStacks])
  have t2 := push_eval a2 10
  have t3 := copy_eval a3 35 15 (by decide) (by decide) (by decide)
    (by simp +decide [a3, a2, a1, a, pushed, TupleProgram.pushedState, copied, copyStacks,
      coefficientResult, install, MatrixPascalProgram.resting, MatrixPascalProgram.stage,
      MatrixPascalProgram.frame, MatrixPascalProgram.extend,
      MatrixScalarProgram.scalarStacks])
  have hs : a4.stacks 12 = CoefficientPascalProgram.valueWords p ys := by
    simp +decide [a4, a3, a2, a1, a, pushed, TupleProgram.pushedState, copied, copyStacks,
      coefficientResult, install, MatrixPascalProgram.resting, MatrixPascalProgram.stage,
      MatrixPascalProgram.frame, MatrixPascalProgram.extend,
      MatrixScalarProgram.scalarStacks]
  have hi : (a4.stacks 15).length = A := by
    simp +decide [a4, a3, a2, a1, a, pushed, TupleProgram.pushedState, copied, copyStacks,
      coefficientResult, install, prepared, MatrixPascalProgram.resting,
      MatrixPascalProgram.stage, MatrixPascalProgram.frame, MatrixPascalProgram.extend,
 MatrixScalarProgram.scalarStacks]
  have hw : (a4.stacks 10).length = 2 * width p + 1 := by
    simp +decide [a4, a3, a2, a1, pushed, TupleProgram.pushedState, copied, copyStacks,
      ha10, ha30]
    omega
  have hz : ∀ j ∈ ([0, 2, 3, 4, 6, 9, 13] : List (Fin 37)), a4.stacks j = [] := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp +decide [a4, a3, a2, a1, a, pushed, TupleProgram.pushedState, copied, copyStacks,
        coefficientResult, install, prepared, MatrixPascalProgram.resting,
        MatrixPascalProgram.stage, MatrixPascalProgram.frame, MatrixPascalProgram.extend,
 MatrixScalarProgram.scalarStacks]
  obtain ⟨ns, hns, b, ts, hbs⟩ := selectWord_eval p a4 ys A hA hs hi hw
    (hz 0 (by simp)) (hz 2 (by simp)) (hz 3 (by simp)) (hz 4 (by simp))
    (hz 6 (by simp)) (hz 9 (by simp)) (hz 13 (by simp))
  have hl : ∀ j, b.stacks (signedStacks j) =
      (MatrixSignedWordProgram.state p b.regs (ys.getD A 0) (List.replicate A true)).stacks j := by
    intro j
    rw [hbs]
    fin_cases j <;>
      simp +decide [signedStacks, MatrixSignedWordProgram.state, a4, a3, a2, a1, a,
        pushed, TupleProgram.pushedState, copied, copyStacks, coefficientResult,
        install, prepared, MatrixPascalProgram.resting, MatrixPascalProgram.stage,
        MatrixPascalProgram.frame, MatrixPascalProgram.extend,
        MatrixScalarProgram.scalarStacks]
  obtain ⟨nn, hnn, out, tn⟩ := signedWord_eval p b (ys.getD A 0) (List.replicate A true) hl
  let c := signedResult b out p ((-1 : ZMod p)^(List.replicate A true).length * ys.getD A 0)
  have hc : c = finished base out p ys A B := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      simp only [ hbs]
      fin_cases j <;>
        simp +decide [ frameWidthWord, a4, a3, a2, a1, a,
          pushed, TupleProgram.pushedState, copied, copyStacks, coefficientResult,
          install, prepared, MatrixPascalProgram.resting, MatrixPascalProgram.stage,
          MatrixPascalProgram.frame, MatrixPascalProgram.extend,
          MatrixScalarProgram.scalarStacks, hzero]
  have he := t0.seq (t1.seq (t2.seq (t3.seq (ts.seq
    (tn.seq (Eval.base (StructuredProgram.Eval.skip c)))))))
  rw [hc] at he
  refine ⟨(7 * width p + 5) + ((7 * width p + 5) + (2 + ((7 * A + 5) +
    (ns + (nn + 0))))), ?_, out, ?_⟩
  · simp only [List.length_replicate] at hnn
    dsimp [finishEntryCost]
    omega
  · simpa only [finishEntry, series] using
      (show Eval (series [copy 30 10, copy 30 10, push 10, copy 35 15,
        callLow MatrixWordSelectProgram.program (by decide), signedWord])
        ((7 * width p + 5) + ((7 * width p + 5) + (2 + ((7 * A + 5) +
          (ns + (nn + 0)))))) a (finished base out p ys A B) by
        convert he using 1 <;> first
          | rfl
          | omega
          | (simp +decide [a3, a2, a1, a, pushed, TupleProgram.pushedState, copied,
              copyStacks, coefficientResult, install, prepared, hzero]))

open BitProgram StructuredCalls StackRoutines MatrixWordEncoding

def clearResult : List (Fin 37) → Data → Data
  | [], a => a
  | j :: js, a => clearResult js (cleared a j)

def clearCost : List (Fin 37) → Data → ℕ
  | [], _ => 0
  | j :: js, a => 2 * (a.stacks j).length + 3 + clearCost js (cleared a j)

theorem clearMany_eval (js : List (Fin 37)) (a : Data) :
    Eval (series (js.map clear)) (clearCost js a) a (clearResult js a) := by
  induction js generalizing a with
  | nil => exact Eval.base (StructuredProgram.Eval.skip _)
  | cons j js ih => exact (clear_eval a j).seq (ih (cleared a j))

theorem clearResult_stacks (js : List (Fin 37)) (a : Data) (j : Fin 37) :
    (clearResult js a).stacks j = if j ∈ js then [] else a.stacks j := by
  induction js generalizing a with
  | nil => simp [clearResult]
  | cons k ks ih =>
      rw [clearResult, ih]
      by_cases hjk : j = k <;> by_cases hj : j ∈ ks <;>
        simp [hjk, hj, cleared, clearStacks]

theorem clearCost_le (js : List (Fin 37)) (a : Data) :
    clearCost js a ≤ (js.map (fun j => 2 * (a.stacks j).length + 3)).sum := by
  induction js generalizing a with
  | nil => simp [clearCost]
  | cons j js ih =>
      simp only [clearCost, List.map_cons, List.sum_cons]
      apply Nat.add_le_add_left
      refine (ih _).trans ?_
      apply List.sum_le_sum
      intro n hn
      by_cases h : n = j
      · simp [h, cleared, clearStacks]
      · simp [h, cleared, clearStacks]

def cleanupCost (a : Data) : ℕ :=
  (cleanupPorts.map (fun j => 2 * (a.stacks j).length + 3)).sum +
    (7 * (a.stacks 33).length + 5) + (2 * (a.stacks 33).length + 3)

def cleaned (a : Data) (out : Fin 9 → Bool) : Data :=
  ⟨out, Function.update (Function.update
    (fun j => if j ∈ cleanupPorts then [] else a.stacks j) 22 (a.stacks 33)) 33 []⟩

theorem cleanup_eval (a : Data) (h9 : a.stacks 9 = []) (h22 : a.stacks 22 = []) :
    ∃ n ≤ cleanupCost a, ∃ out, Eval cleanup n a (cleaned a out) := by
  let b := clearResult cleanupPorts a
  let c := copied b 33 22
  let d := cleared c 33
  have t0 := clearMany_eval cleanupPorts a
  have t1 := copy_eval b 33 22 (by decide) (by decide) (by decide)
    (by simp [b, clearResult_stacks, cleanupPorts, h9])
  have t2 := clear_eval c 33
  have hb22 : b.stacks 22 = [] := by simp [b, clearResult_stacks, cleanupPorts, h22]
  have hb33 : b.stacks 33 = a.stacks 33 := by simp [b, clearResult_stacks, cleanupPorts]
  have hc33 : c.stacks 33 = a.stacks 33 := by simp [c, copied, copyStacks, hb33]
  have hd : d = cleaned a d.regs := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      simp only [ c, copied, clearStacks]
      by_cases h33 : j = 33
      · subst j; simp
      by_cases h22 : j = 22
      · subst j; simp [copyStacks, hb22, hb33]
      · simp [copyStacks, h33, h22, b, clearResult_stacks]
  change cleared c 33 = cleaned a d.regs at hd
  have he := t0.seq (t1.seq t2)
  rw [hd] at he
  refine ⟨clearCost cleanupPorts a +
    ((7 * (a.stacks 33).length + 5) + (2 * (a.stacks 33).length + 3)), ?_, d.regs, ?_⟩
  · have h := clearCost_le cleanupPorts a
    dsimp [cleanupCost]
    omega
  · simpa only [cleanup, hb33, hc33] using he

theorem cleaned_finished (base : Data) (regs out : Fin 9 → Bool) (p : ℕ) [Fact p.Prime]
    (ys : List (ZMod p)) (A B : ℕ)
    (hclear : ∀ j : Fin 37, j.val < 21 → base.stacks j = [])
    (h33 : base.stacks 33 = []) (h34 : base.stacks 34 = [])
    (h35 : base.stacks 35 = []) (h36 : base.stacks 36 = []) :
    cleaned (finished base regs p ys A B) out =
      output base out (word p ((-1 : ZMod p)^A * ys.getD A 0)) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    fin_cases j <;>
      simp +decide [ finished, coefficientResult, install, prepared, cleanupPorts,
 MatrixPascalProgram.resting, MatrixPascalProgram.stage,
        MatrixPascalProgram.frame, MatrixPascalProgram.extend,
        MatrixScalarProgram.scalarStacks, hclear, h33, h34, h35, h36]

end SubexponentialSAT.Subexp.MatrixEntryProgram

end OAI.Algorithms
