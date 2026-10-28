import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularPrograms
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-!
# Preserving saturating binary subtraction

Eight Boolean registers and eight stacks suffice. The two operands remain
on stacks 0 and 1; stack 2 receives their natural-number difference and
stacks 3 through 7 return empty. Copied concatenations supply a common
padding shape without computing a numeric width. The final borrow bit
controls a real clear loop. Every copy, pad, subtraction, and clear is
charged in the linear instruction bound.
-/

namespace SubexponentialSAT.SaturatingSubtractionProgram

open BitProgram StructuredCalls BinaryArithmetic ModularArithmetic

abbrev Data := State 8 8
abbrev Code := Cmd 8 8

abbrev store (regs : Fin 8 → Bool) (xs ys w₂ w₃ w₄ w₅ w₆ : List Bool) : Data :=
  ⟨regs, ![xs, ys, w₂, w₃, w₄, w₅, w₆, []]⟩

abbrev state (regs : Fin 8 → Bool) (xs ys output : List Bool) : Data :=
  store regs xs ys output [] [] [] []

def copy (src dst : Fin 8) : Code :=
  .call (StackRoutines.copyProgram src dst 6 0 1)

abbrev copied (src dst : Fin 8) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

theorem copy_eval (src dst : Fin 8) (d : Data)
    (hsd : src ≠ dst) (hs6 : src ≠ 6) (h6d : (6 : Fin 8) ≠ dst)
    (h6 : d.stacks 6 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied src dst d) := by
  apply Eval.call
  exact ListRegisterProgram.copy_run src dst 6 0 1 hsd hs6 h6d (by decide)
    d.regs d.stacks h6

def three (d : Data) (regs : Fin 8 → Bool) (p : Fin 3 → Fin 8)
    (a b c : List Bool) : Data :=
  ⟨regs, Function.update (Function.update (Function.update d.stacks (p 0) a) (p 1) b) (p 2) c⟩

theorem embed_three (p : Fin 3 → Fin 8) (hp : Function.Injective p)
    (d : Data) (regs : Fin 8 → Bool) (a b c : List Bool) :
    embedState id p d ⟨regs, ModularPrograms.operandStacks a b c⟩ = three d regs p a b c := by
  apply embedState_eq_of_ports id p d _ _ Function.injective_id hp
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [three, ModularPrograms.operandStacks, hp.eq_iff]
  · intro i hi
    have h0 : i ≠ p 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ p 1 := fun h => hi ⟨1, h.symm⟩
    have h2 : i ≠ p 2 := fun h => hi ⟨2, h.symm⟩
    simp [three, h0, h1, h2]

theorem project_three (p : Fin 3 → Fin 8) (d : Data) (h2 : d.stacks (p 2) = []) :
    projectState id p d =
      ⟨d.regs, ModularPrograms.operandStacks (d.stacks (p 0)) (d.stacks (p 1)) []⟩ := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [ ModularPrograms.operandStacks, h2]

def padAt (p : Fin 3 → Fin 8) : Code :=
  .call (ProgramLinking.liftProgram ModularPrograms.paddingLEProgram id p)

theorem padAt_eval (p : Fin 3 → Fin 8) (hp : Function.Injective p) (d : Data)
    (h2 : d.stacks (p 2) = [])
    (hlen : (d.stacks (p 1)).length ≤ (d.stacks (p 0)).length) :
    ∃ regs, Eval (padAt p) (7 * (d.stacks (p 0)).length + 6) d
      (three d regs p (padTo (d.stacks (p 0)) (d.stacks (p 1))) [] []) := by
  obtain ⟨regs, ht, _⟩ := ModularPrograms.paddingLE_correct d.regs
    (d.stacks (p 0)) (d.stacks (p 1)) hlen
  have htrace : Trace ModularPrograms.paddingLEProgram
      (7 * (d.stacks (p 0)).length + 6)
      ((projectState id p d).withPC (some ModularPrograms.paddingLEProgram.entry))
      ((⟨regs, ModularPrograms.operandStacks
        (padTo (d.stacks (p 0)) (d.stacks (p 1))) [] []⟩ : State 8 3).withPC none) := by
    rw [project_three p d h2]
    exact ht
  have he := eval_call_from_state ModularPrograms.paddingLEProgram id p d
    Function.injective_id hp htrace
  rw [embed_three p hp] at he
  exact ⟨regs, he⟩

def subtractAt (p : Fin 3 → Fin 8) : Code :=
  .call (ProgramLinking.liftProgram ModularPrograms.subtractLEProgram id p)

theorem subtractAt_eval (p : Fin 3 → Fin 8) (hp : Function.Injective p) (d : Data)
    (h2 : d.stacks (p 2) = []) (h0 : d.regs 0 = false)
    (hlen : (d.stacks (p 0)).length = (d.stacks (p 1)).length) :
    ∃ regs, Eval (subtractAt p) (15 * (d.stacks (p 0)).length + 6) d
      (three d regs p (subCarry false (d.stacks (p 0)) (d.stacks (p 1))).1 [] []) ∧
      regs 0 = (subCarry false (d.stacks (p 0)) (d.stacks (p 1))).2 := by
  obtain ⟨regs, ht, hb⟩ := ModularPrograms.subtractLE_correct d.regs
    (d.stacks (p 0)) (d.stacks (p 1)) hlen
  rw [h0] at ht hb
  have htrace : Trace ModularPrograms.subtractLEProgram
      (15 * (d.stacks (p 0)).length + 6)
      ((projectState id p d).withPC (some ModularPrograms.subtractLEProgram.entry))
      ((⟨regs, ModularPrograms.operandStacks
        (subCarry false (d.stacks (p 0)) (d.stacks (p 1))).1 [] []⟩ : State 8 3).withPC none) := by
    rw [project_three p d h2]
    exact ht
  have he := eval_call_from_state ModularPrograms.subtractLEProgram id p d
    Function.injective_id hp htrace
  rw [embed_three p hp] at he
  exact ⟨regs, he, hb⟩

def leftPorts : Fin 3 → Fin 8 := ![2, 4, 6]
def rightPorts : Fin 3 → Fin 8 := ![3, 5, 6]
def subtractPorts : Fin 3 → Fin 8 := ![2, 3, 6]

theorem leftPorts_injective : Function.Injective leftPorts := by decide
theorem rightPorts_injective : Function.Injective rightPorts := by decide
theorem subtractPorts_injective : Function.Injective subtractPorts := by decide

local infixr:60 " ;; " => Cmd.seq

def prepare : Code := copy 1 2 ;; copy 0 2 ;; copy 1 3 ;; copy 0 3 ;; copy 0 4 ;; copy 1 5

theorem prepare_eval (regs : Fin 8 → Bool) (xs ys : List Bool) :
    Eval prepare (21 * (xs.length + ys.length) + 30) (state regs xs ys [])
      (store (readRegs regs 0 1 none) xs ys (xs ++ ys) (xs ++ ys) xs ys []) := by
  let d₀ := state regs xs ys []
  let d₁ := copied 1 2 d₀
  let d₂ := copied 0 2 d₁
  let d₃ := copied 1 3 d₂
  let d₄ := copied 0 3 d₃
  let d₅ := copied 0 4 d₄
  let d₆ := copied 1 5 d₅
  have h₁ := copy_eval 1 2 d₀ (by decide) (by decide) (by decide) (by rfl)
  have h₂ := copy_eval 0 2 d₁ (by decide) (by decide) (by decide) (by rfl)
  have h₃ := copy_eval 1 3 d₂ (by decide) (by decide) (by decide) (by rfl)
  have h₄ := copy_eval 0 3 d₃ (by decide) (by decide) (by decide) (by rfl)
  have h₅ := copy_eval 0 4 d₄ (by decide) (by decide) (by decide) (by rfl)
  have h₆ := copy_eval 1 5 d₅ (by decide) (by decide) (by decide) (by rfl)
  have hend : d₆ = store (readRegs regs 0 1 none) xs ys
      (xs ++ ys) (xs ++ ys) xs ys [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [ d₅, d₄, d₃, d₂, d₁, d₀, StackRoutines.readRegs_reset]
    · funext i
      fin_cases i <;>
        simp [ d₅, d₄, d₃, d₂, d₁, d₀, StackRoutines.copyStacks]
  have he := h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq h₆))))
  change Eval prepare _ (state regs xs ys []) d₆ at he
  rw [hend] at he
  convert he using 1
  simp [d₅, d₄, d₃, d₂, d₁, d₀, StackRoutines.copyStacks]
  omega

def clearOutput : Code := .call (StackRoutines.clearProgram 2 0 1)
def finish : Code := .ite 0 clearOutput (.base .skip) ;; RegisterResetProgram.all

theorem finish_eval (regs : Fin 8 → Bool) (xs ys output : List Bool) :
    ∃ t ≤ 2 * output.length + 12,
      Eval finish t (state regs xs ys output)
        (state (fun _ => false) xs ys (if regs 0 then [] else output)) := by
  cases hb : regs 0 with
  | false =>
      have hs : Eval (.ite 0 clearOutput (.base .skip)) 1
          (state regs xs ys output) (state regs xs ys output) :=
        .ite_false hb (.base (.skip _))
      refine ⟨9, by omega, ?_⟩
      simpa only [finish, hb, Bool.false_eq_true, ↓reduceIte] using
        hs.seq (RegisterResetProgram.all_eval (state regs xs ys output))
  | true =>
      have hc : Eval clearOutput (2 * output.length + 3) (state regs xs ys output)
          (state (readRegs regs 0 1 none) xs ys []) := by
        apply Eval.call
        have h := ListRegisterProgram.clear_run (2 : Fin 8) (0 : Fin 8) 1
          regs (state regs xs ys output).stacks
        have hstack : StackRoutines.clearStacks (2 : Fin 8) (state regs xs ys output).stacks =
            (state (readRegs regs 0 1 none) xs ys []).stacks := by
          funext i
          fin_cases i <;> simp [ StackRoutines.clearStacks]
        unfold ListRegisterProgram.Run at h
        rw [hstack] at h
        exact h
      have hi := Eval.ite_true (no := (.base .skip : Code)) hb hc
      refine ⟨2 * output.length + 12, le_rfl, ?_⟩
      simpa only [finish, hb, ↓reduceIte, Nat.add_assoc] using
        hi.seq (RegisterResetProgram.all_eval (state (readRegs regs 0 1 none) xs ys []))

def saturated (xs ys : List Bool) : List Bool :=
  if (subCarry false xs ys).2 then [] else (subCarry false xs ys).1

theorem saturated_value (xs ys : List Bool) (hlen : xs.length = ys.length) :
    BinaryArithmetic.toNat (saturated xs ys) = BinaryArithmetic.toNat xs - BinaryArithmetic.toNat ys := by
  have hc := subCarry_correct false xs ys hlen
  cases hb : (subCarry false xs ys).2 with
  | false =>
      simp only [hb, bitVal, Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.add_zero] at hc
      simp only [saturated, hb, Bool.false_eq_true, ↓reduceIte]
      omega
  | true =>
      have hlt := (subCarry_borrow_iff xs ys hlen).mp hb
      simp [saturated, hb, Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]

theorem saturated_length (xs ys : List Bool) (hlen : xs.length = ys.length) :
    (saturated xs ys).length ≤ xs.length := by
  cases hb : (subCarry false xs ys).2 <;>
    simp [saturated, hb, subCarry_length false xs ys hlen]

def setBorrow : Code := .base (.atom (.set 0 false))

def command : Code :=
  prepare ;; padAt leftPorts ;; padAt rightPorts ;; setBorrow ;; subtractAt subtractPorts ;; finish

def program := compiled command 0 2

/-- Both numeric operands are preserved. The sole output is natural-number
subtraction, and its representation length is bounded by the input lengths.
The instruction allowance includes the final compiled halt. -/
theorem command_eval (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ (t : ℕ) (word : List Bool),
      t + 1 ≤ 100 * (xs.length + ys.length + 1) ∧
      Eval command t (state regs xs ys []) (state (fun _ => false) xs ys word) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat xs - BinaryArithmetic.toNat ys ∧ word.length ≤ xs.length + ys.length := by
  let shape := xs ++ ys
  let px := padTo shape xs
  let py := padTo shape ys
  have hx : xs.length ≤ shape.length := by simp [shape]
  have hy : ys.length ≤ shape.length := by simp [shape]
  have hlen : px.length = py.length := by simp [px, py, padTo_length]
  let a := store (readRegs regs 0 1 none) xs ys shape shape xs ys []
  obtain ⟨r₁, hp₁⟩ := padAt_eval leftPorts leftPorts_injective a (by rfl) hx
  let b := store r₁ xs ys px shape [] ys []
  have eb : three a r₁ leftPorts (padTo (a.stacks (leftPorts 0))
      (a.stacks (leftPorts 1))) [] [] = b := by
    apply congrArg (StructuredProgram.State.mk r₁)
    funext i
    fin_cases i <;> simp [ a, leftPorts, px]
  rw [eb] at hp₁
  obtain ⟨r₂, hp₂⟩ := padAt_eval rightPorts rightPorts_injective b (by rfl) hy
  let c := store r₂ xs ys px py [] [] []
  have ec : three b r₂ rightPorts (padTo (b.stacks (rightPorts 0))
      (b.stacks (rightPorts 1))) [] [] = c := by
    apply congrArg (StructuredProgram.State.mk r₂)
    funext i
    fin_cases i <;> simp [ b, rightPorts, py]
  rw [ec] at hp₂
  let d := store (Function.update r₂ 0 false) xs ys px py [] [] []
  have hs : Eval setBorrow 1 c d := .base (.atom _ _)
  obtain ⟨r₃, hd, hb⟩ := subtractAt_eval subtractPorts subtractPorts_injective d
    (by rfl) (by simp [d ]) hlen
  let diff := (subCarry false px py).1
  have ee : three d r₃ subtractPorts (subCarry false (d.stacks (subtractPorts 0))
      (d.stacks (subtractPorts 1))).1 [] [] = state r₃ xs ys diff := by
    apply congrArg (StructuredProgram.State.mk r₃)
    funext i
    fin_cases i <;> simp [ d, subtractPorts, diff]
  rw [ee] at hd
  change r₃ 0 = (subCarry false px py).2 at hb
  obtain ⟨tf, htf, hf⟩ := finish_eval r₃ xs ys diff
  rw [hb] at hf
  change Eval finish tf (state r₃ xs ys diff)
    (state (fun _ => false) xs ys (saturated px py)) at hf
  have he := (prepare_eval regs xs ys).seq (hp₁.seq (hp₂.seq (hs.seq (hd.seq hf))))
  let t := (21 * (xs.length + ys.length) + 30) +
    ((7 * shape.length + 6) + ((7 * shape.length + 6) + (1 + ((15 * px.length + 6) + tf))))
  change Eval command t (state regs xs ys [])
    (state (fun _ => false) xs ys (saturated px py)) at he
  refine ⟨t, saturated px py, ?_, he, ?_, ?_⟩
  · have hdiff : diff.length = shape.length :=
      (subCarry_length false px py hlen).trans (padTo_length shape xs)
    rw [hdiff] at htf
    dsimp [t]
    rw [padTo_length]
    simp only [shape, List.length_append] at htf ⊢
    omega
  · rw [saturated_value px py hlen, padTo_correct shape xs hx, padTo_correct shape ys hy]
  · exact (saturated_length px py hlen).trans_eq (by simp [px, shape, padTo_length])

theorem program_runs (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ word, RunsIn program (100 * (xs.length + ys.length + 1))
      ((state regs xs ys []).withPC (some program.entry))
      ((state (fun _ => false) xs ys word).withPC none) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat xs - BinaryArithmetic.toNat ys ∧ word.length ≤ xs.length + ys.length := by
  obtain ⟨t, word, ht, he, hv, hl⟩ := command_eval regs xs ys
  exact ⟨word, ⟨t + 1, ht, compiled_halt_trace he 0 2⟩, hv, hl⟩

end SubexponentialSAT.SaturatingSubtractionProgram

end OAI.Algorithms
