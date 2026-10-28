import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientPascalProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Repeated adjacent additions for a normalized matrix entry. The number of
passes and the coefficient-row length are unary runtime data. Every pass calls
the fixed modular Pascal program and physically replaces the working row. -/

namespace SubexponentialSAT.Subexp.MatrixPascalProgram

open BitProgram StructuredCalls StackRoutines
open MatrixWordEncoding

abbrev Data := State 8 18

def lowPorts : Fin 16 → Fin 18 := Fin.castAdd 2

theorem lowPorts_injective : Function.Injective lowPorts := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 18 => k.val) h

def extend (bank : Fin 16 → List Bool) (todo widthCount : List Bool) :
    Fin 18 → List Bool :=
  ![bank 0, bank 1, bank 2, bank 3, bank 4, bank 5, bank 6, bank 7,
    bank 8, bank 9, bank 10, bank 11, bank 12, bank 13, bank 14, bank 15,
    todo, widthCount]

def frame (a : MatrixScalarProgram.Data) (todo widthCount : List Bool) : Data :=
  ⟨a.regs, extend a.stacks todo widthCount⟩

theorem embed_frame (base a : MatrixScalarProgram.Data) (todo widthCount : List Bool) :
    embedState id lowPorts (frame base todo widthCount) a = frame a todo widthCount := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id lowPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro j hj
    have hge : 16 ≤ j.val := by
      by_contra h
      exact hj ⟨⟨j.val, by omega⟩, Fin.ext rfl⟩
    fin_cases j <;> norm_num [frame, extend] at *

abbrev pascal : Cmd 8 18 := .call
  (ProgramLinking.liftProgram (CoefficientPascalProgram.program false) id lowPorts)

variable (p : ℕ) [Fact p.Prime]

def stage (regs : Fin 8 → Bool) (xs : List (ZMod p))
    (acc input todo widthCount : List Bool) : Data :=
  frame (MatrixScalarProgram.state regs [] [] (modulus p) acc [] []
    (CoefficientPascalProgram.valueWords p xs) [] (word p 0) input) todo widthCount

def resting (regs : Fin 8 → Bool) (xs : List (ZMod p)) (todo : List Bool) : Data :=
  stage p regs xs [] [] todo (List.replicate xs.length true)

theorem pascal_eval (xs : List (ZMod p)) (regs : Fin 8 → Bool)
    (todo widthCount : List Bool) :
    ∃ n ≤ CoefficientPascalProgram.budget xs.length (width p), ∃ regs',
      Eval pascal n
        (stage p regs xs [] (List.replicate xs.length true) todo widthCount)
        (stage p regs' xs
          (CoefficientPascalProgram.valueWords p (CoefficientPascalProgram.shiftBy p false xs))
          [] todo widthCount) := by
  obtain ⟨regs', n, hn, ht⟩ := CoefficientPascalProgram.program_run p false xs regs
  let base := MatrixScalarProgram.state regs [] [] (modulus p) [] [] []
    (CoefficientPascalProgram.valueWords p xs) [] (word p 0)
    (List.replicate xs.length true)
  have he := eval_call_lifted (CoefficientPascalProgram.program false) id lowPorts
    (frame base todo widthCount) Function.injective_id lowPorts_injective ht
  rw [embed_frame, embed_frame] at he
  exact ⟨n, hn, regs', he⟩

abbrev pass : Cmd 8 18 :=
  .seq (MatrixProgramSupport.copy 17 15 9)
    (.seq pascal (.seq (.call (clearProgram 12 0 1))
      (MatrixProgramSupport.move 8 12 9)))

def passBudget (R B : ℕ) : ℕ :=
  7 * R + 5 + CoefficientPascalProgram.budget R B + 8 * (R * (2 * B + 1)) + 9

theorem pass_eval (xs : List (ZMod p)) (regs : Fin 8 → Bool) (todo : List Bool) :
    ∃ n ≤ passBudget xs.length (width p), ∃ regs',
      Eval pass n (resting p regs xs todo)
        (resting p regs' (CoefficientPascalProgram.shiftBy p false xs) todo) := by
  obtain ⟨a, ha, hsa⟩ := MatrixProgramSupport.copy_eval (17 : Fin 18) 15 9
    (by decide) (by decide) (by decide) (resting p regs xs todo) rfl
  have hA : a = stage p a.regs xs [] (List.replicate xs.length true) todo
      (List.replicate xs.length true) := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsa]
    funext j
    fin_cases j <;> simp [resting, stage, frame, extend,
      MatrixScalarProgram.scalarStacks, copyStacks]
  rw [hA] at ha
  obtain ⟨np, hnp, rp, hp⟩ := pascal_eval p xs a.regs todo (List.replicate xs.length true)
  let b := stage p rp xs
    (CoefficientPascalProgram.valueWords p (CoefficientPascalProgram.shiftBy p false xs))
    [] todo (List.replicate xs.length true)
  have hc := TupleProgram.clear_eval (12 : Fin 18) (0 : Fin 8) 1 b
  let c : Data := ⟨readRegs b.regs 0 1 none, clearStacks 12 b.stacks⟩
  change Eval (.call (clearProgram 12 0 1)) (2 * (b.stacks 12).length + 3) b c at hc
  obtain ⟨d, hd, hsd⟩ := MatrixProgramSupport.move_eval (8 : Fin 18) 12 9
    (by decide) (by decide) (by decide) c
    (by simp [c, clearStacks])
    (by simp [c, b, stage, frame, extend,
      MatrixScalarProgram.scalarStacks, clearStacks])
  have hD : d = resting p d.regs (CoefficientPascalProgram.shiftBy p false xs) todo := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsd]
    funext j
    fin_cases j <;> simp [resting, c, b, stage, frame, extend,
      MatrixScalarProgram.scalarStacks, clearStacks]
  rw [hD] at hd
  have he := ha.seq (hp.seq (hc.seq hd))
  refine ⟨7 * xs.length + 5 + (np +
    ((2 * (CoefficientPascalProgram.valueWords p xs).length + 3) +
      (6 * (CoefficientPascalProgram.valueWords p
        (CoefficientPascalProgram.shiftBy p false xs)).length + 6))), ?_, d.regs, ?_⟩
  · simp only [CoefficientPascalProgram.valueWords_length,
      CoefficientPascalProgram.shiftBy_length]
    dsimp [passBudget]
    omega
  · simpa [pass, resting, b, c, stage, frame, extend,
      MatrixScalarProgram.state, MatrixScalarProgram.scalarStacks,
      clearStacks] using he

abbrev popCount : Cmd 8 18 := .base (.atom (.pop 16 0 1))
abbrev body : Cmd 8 18 := .seq pass popCount
abbrev loop : Cmd 8 18 := .while 1 body
abbrev command : Cmd 8 18 := .seq popCount loop

def ready (regs : Fin 8 → Bool) (xs : List (ZMod p)) (n : ℕ) : Data :=
  resting p (readRegs regs 0 1 (List.replicate n true).head?) xs
    (List.replicate n true).tail

theorem popCount_eval (regs : Fin 8 → Bool) (xs : List (ZMod p)) (n : ℕ) :
    Eval popCount 1 (resting p regs xs (List.replicate n true)) (ready p regs xs n) := by
  have he := Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.pop (16 : Fin 18) 0 1) (resting p regs xs (List.replicate n true)))
  convert he using 1
  apply MatrixProgramSupport.data_ext
  · rfl
  · funext j
    fin_cases j <;> simp [ready, resting, stage, frame, extend, MatrixScalarProgram.scalarStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]

theorem ready_zero (regs : Fin 8 → Bool) (xs : List (ZMod p)) :
    (ready p regs xs 0).regs 1 = false := by
  simp [ready, resting, stage, frame, readRegs]

theorem ready_succ (regs : Fin 8 → Bool) (xs : List (ZMod p)) (n : ℕ) :
    (ready p regs xs (n + 1)).regs 1 = true := by
  simp [ready, resting, stage, frame, readRegs,
    List.replicate_succ]

def repeated : ℕ → List (ZMod p) → List (ZMod p)
  | 0, xs => xs
  | n + 1, xs => repeated n (CoefficientPascalProgram.shiftBy p false xs)

@[simp] theorem repeated_length (n : ℕ) (xs : List (ZMod p)) :
    (repeated p n xs).length = xs.length := by
  induction n generalizing xs <;> simp [repeated, *]

theorem loop_eval (n : ℕ) (xs : List (ZMod p)) (regs : Fin 8 → Bool) :
    ∃ t ≤ n * (passBudget xs.length (width p) + 2) + 1, ∃ regs',
      Eval loop t (ready p regs xs n) (resting p regs' (repeated p n xs) []) := by
  induction n generalizing xs regs with
  | zero =>
      refine ⟨1, by simp, (ready p regs xs 0).regs, ?_⟩
      have hz : resting p (ready p regs xs 0).regs xs [] = ready p regs xs 0 := by
        apply congrArg (StructuredProgram.State.mk _)
        funext i
        fin_cases i <;>
          simp [ extend ]
      simp only [repeated]
      rw [hz]
      exact Eval.while_false (body := body) (ready_zero p regs xs)
  | succ n ih =>
      obtain ⟨np, hnp, rp, hp⟩ := pass_eval p xs (ready p regs xs (n + 1)).regs
        (List.replicate n true)
      have hstart : resting p (ready p regs xs (n + 1)).regs xs (List.replicate n true) =
          ready p regs xs (n + 1) := by
        simp [ready, resting, stage, frame, List.replicate_succ]
      rw [hstart] at hp
      have hc := popCount_eval p rp (CoefficientPascalProgram.shiftBy p false xs) n
      obtain ⟨nt, hnt, rf, ht⟩ := ih (CoefficientPascalProgram.shiftBy p false xs) rp
      have he := Eval.while_true (ready_succ p regs xs n) (hp.seq hc) ht
      refine ⟨(np + 1) + nt + 1, ?_, rf, he⟩
      simp only [CoefficientPascalProgram.shiftBy_length] at hnt
      simp only [Nat.succ_mul]
      omega

def program := compiled command 12 12

theorem program_runsIn (n : ℕ) (xs : List (ZMod p)) (regs : Fin 8 → Bool) :
    ∃ regs', RunsIn program (n * (passBudget xs.length (width p) + 2) + 3)
      ((resting p regs xs (List.replicate n true)).withPC (some program.entry))
      ((resting p regs' (repeated p n xs) []).withPC none) := by
  obtain ⟨nt, hnt, rf, ht⟩ := loop_eval p n xs regs
  have he := (popCount_eval p regs xs n).seq ht
  exact ⟨rf, 1 + nt + 1, by omega, compiled_halt_trace he 12 12⟩

end SubexponentialSAT.Subexp.MatrixPascalProgram

end OAI.Algorithms
