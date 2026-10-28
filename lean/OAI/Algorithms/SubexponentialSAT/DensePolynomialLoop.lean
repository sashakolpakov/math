import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing

namespace OAI.Algorithms

/-! A fixed streaming array loop, parameterized by a finite word program
and an actual trace theorem for one word. The concrete modular-word
instantiation is supplied in DensePolynomialPrograms. -/

namespace SubexponentialSAT.DensePolynomialLoop

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

abbrev Data := State 8 20

def stackArray (x y modulus left right width counter tmp packed : List Bool)
    (frame : Fin 6 → List Bool) : Fin 20 → List Bool :=
  fun i => Fin.addCases (m := 14) (n := 6) (motive := fun _ => List Bool)
    (![x,y,[],[],[],modulus,[],[],left,right,width,counter,tmp,packed] : Fin 14 → List Bool) frame i

def state (regs : Fin 8 → Bool)
    (x y modulus left right width counter tmp packed : List Bool)
    (frame : Fin 6 → List Bool) : Data :=
  ⟨regs, stackArray x y modulus left right width counter tmp packed frame⟩

def ready (regs : Fin 8 → Bool) (modulus left right width packed : List Bool)
    (frame : Fin 6 → List Bool) : Data :=
  state regs [] [] modulus left right width [] [] packed frame

abbrev guard : Cmd 8 20 :=
  .seq (.base (.atom (.peek 8 0 1)))
    (.seq (.base (.atom (.peek 9 2 3))) (.base (.atom (.band 4 1 3))))

def guardRegs (regs : Fin 8 → Bool) (left right : List Bool) : Fin 8 → Bool :=
  let r := readRegs (readRegs regs 0 1 left.head?) 2 3 right.head?
  Function.update r 4 (r 1 && r 3)

@[simp] theorem guardRegs_test (regs : Fin 8 → Bool) (left right : List Bool) :
    guardRegs regs left right 4 = (left.head?.isSome && right.head?.isSome) := by
  simp [guardRegs, readRegs]

theorem guard_eval (regs : Fin 8 → Bool) (modulus left right width packed : List Bool)
    (frame : Fin 6 → List Bool) :
    Eval guard 3 (ready regs modulus left right width packed frame)
      (ready (guardRegs regs left right) modulus left right width packed frame) := by
  let d := ready regs modulus left right width packed frame
  have h₁ := Eval.base (StructuredProgram.Eval.atom (r := 8) (s := 20) (.peek 8 0 1) d)
  have h₂ := Eval.base (StructuredProgram.Eval.atom (r := 8) (s := 20) (.peek 9 2 3)
    ((StructuredProgram.Atom.peek 8 0 1).eval d))
  have h₃ := Eval.base (StructuredProgram.Eval.atom (r := 8) (s := 20) (.band 4 1 3)
    ((StructuredProgram.Atom.peek 9 2 3).eval ((StructuredProgram.Atom.peek 8 0 1).eval d)))
  exact Eval.seq h₁ (Eval.seq h₂ h₃)

abbrev addLoop (step : Cmd 8 20) : Cmd 8 20 := .while 4 (.seq step guard)

abbrev flush : Cmd 8 20 :=
  .seq (.call (StackRoutines.transferProgram 8 13 (0 : Fin 8) 1))
    (.seq (.call (StackRoutines.transferProgram 9 13 (0 : Fin 8) 1))
      (.call (StackRoutines.transferProgram 13 8 (0 : Fin 8) 1)))

abbrev addCmd (step : Cmd 8 20) : Cmd 8 20 := .seq guard (.seq (addLoop step) flush)

abbrev program (step : Cmd 8 20) : Program 8 20 (StructuredCalls.size (addCmd step) + 1) :=
  StructuredCalls.compiled (addCmd step) 8 8

theorem flush_eval (regs : Fin 8 → Bool) (modulus left right width packed : List Bool)
    (frame : Fin 6 → List Bool) :
    Eval flush (6 * left.length + 6 * right.length + 3 * packed.length + 9)
      (ready regs modulus left right width packed frame)
      (ready (readRegs regs 0 1 none) modulus (packed.reverse ++ left ++ right) [] width [] frame) := by
  let d₀ := ready regs modulus left right width packed frame
  let d₁ := ready (readRegs regs 0 1 none) modulus [] right width (left.reverse ++ packed) frame
  let d₂ := ready (readRegs regs 0 1 none) modulus [] [] width
    (right.reverse ++ left.reverse ++ packed) frame
  have h₁ := transfer_eval d₀ 8 13 0 1 (by decide) (by decide)
  have e₁ : afterTransfer d₀ 8 13 0 1 = d₁ := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;>
        simp [afterTransfer, d₀, d₁, ready, state, stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod,
          StackRoutines.transferStacks]
  have h₂ := transfer_eval d₁ 9 13 0 1 (by decide) (by decide)
  have e₂ : afterTransfer d₁ 9 13 0 1 = d₂ := by
    apply state_ext
    · simp [afterTransfer, d₁, d₂, ready, state, StackRoutines.readRegs_reset]
    · funext i; fin_cases i <;>
        simp [afterTransfer, d₁, d₂, ready, state, stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod,
          StackRoutines.transferStacks,
          List.append_assoc]
  have h₃ := transfer_eval d₂ 13 8 0 1 (by decide) (by decide)
  have e₃ : afterTransfer d₂ 13 8 0 1 =
      ready (readRegs regs 0 1 none) modulus (packed.reverse ++ left ++ right) [] width [] frame := by
    apply state_ext
    · simp [afterTransfer, d₂, ready, state, StackRoutines.readRegs_reset]
    · funext i; fin_cases i <;>
        simp [afterTransfer, d₂, ready, state, stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod,
          StackRoutines.transferStacks,
          List.reverse_append, List.append_assoc]
  rw [e₁] at h₁
  rw [e₂] at h₂
  rw [e₃] at h₃
  have h := Eval.seq h₁ (Eval.seq h₂ h₃)
  convert h using 1
  all_goals simp [ d₀, d₁, d₂, ready, state, stackArray, Fin.addCases,
    Fin.coe_ofNat_eq_mod, List.length_append]
  omega

def flatten {B : ℕ} (xs : List (Word B)) : List Bool := (xs.map Subtype.val).flatten

@[simp] theorem flatten_length {B : ℕ} (xs : List (Word B)) :
    (flatten xs).length = xs.length * B := by
  induction xs with
  | nil => simp [flatten]
  | cons x xs ih =>
      change (x.val ++ flatten xs).length = (xs.length + 1) * B
      rw [List.length_append, x.property, ih]
      ring

theorem flatten_cons_ne_nil {B : ℕ} (hB : 0 < B) (x : Word B) (xs : List (Word B)) :
    flatten (x :: xs) ≠ [] := by
  intro h
  have hh := congrArg List.length h
  rw [flatten_length] at hh
  simp only [List.length_cons, List.length_nil] at hh
  nlinarith

theorem head_isSome_of_ne_nil {α : Type*} {xs : List α} (h : xs ≠ []) : xs.head?.isSome = true := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons a xs => rfl

structure WordStep (B : ℕ) where
  cmd : Cmd 8 20
  modulus : List Bool
  add : Word B → Word B → Word B
  cost : ℕ
  run : ∀ (regs : Fin 8 → Bool) (x y : Word B)
    (left right width packed : List Bool) (frame : Fin 6 → List Bool),
    width.length = B → ∃ n ≤ cost, ∃ regs',
      Eval cmd n (ready regs modulus (x.val ++ left) (y.val ++ right) width packed frame)
        (ready regs' modulus left right width ((add x y).val.reverse ++ packed) frame)

variable {B : ℕ} (step : WordStep B)

def addWords : List (Word B) → List (Word B) → List (Word B)
  | x :: xs, y :: ys => step.add x y :: addWords xs ys
  | _, _ => []

theorem addWords_length (xs ys : List (Word (B))) :
    (addWords step xs ys).length = min xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [addWords]
  | cons x xs ih => cases ys <;> simp [addWords, ih]

theorem addLoop_eval (hB : 0 < B) (regs : Fin 8 → Bool)
    (xs ys : List (Word (B)))
    (width packed : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = B) :
    ∃ n ≤ min xs.length ys.length * (step.cost + 4) + 1, ∃ regs',
      Eval (addLoop step.cmd) n
        (ready (guardRegs regs (flatten xs) (flatten ys)) step.modulus
          (flatten xs) (flatten ys) width packed frame)
        (ready regs' step.modulus (flatten (xs.drop ys.length)) (flatten (ys.drop xs.length)) width
          ((flatten (addWords step xs ys)).reverse ++ packed) frame) := by
  induction xs generalizing ys regs packed with
  | nil =>
      refine ⟨1, by simp, guardRegs regs [] (flatten ys), ?_⟩
      simpa [addLoop, flatten, addWords] using
        (Eval.while_false (test := (4 : Fin 8)) (body := .seq step.cmd guard)
          (a := ready (guardRegs regs [] (flatten ys)) step.modulus [] (flatten ys) width packed frame)
          (by simp [ready, state]))
  | cons x xs ih =>
      cases ys with
      | nil =>
          refine ⟨1, by simp, guardRegs regs (flatten (x :: xs)) [], ?_⟩
          simpa [addLoop, flatten, addWords] using
            (Eval.while_false (test := (4 : Fin 8)) (body := .seq step.cmd guard)
              (a := ready (guardRegs regs (flatten (x :: xs)) []) step.modulus
                (flatten (x :: xs)) [] width packed frame) (by simp [ready, state]))
      | cons y ys =>
          let rg := guardRegs regs (flatten (x :: xs)) (flatten (y :: ys))
          have ht : (ready rg step.modulus (flatten (x :: xs)) (flatten (y :: ys)) width packed frame).regs 4 = true := by
            simp only [ready, state, rg, guardRegs_test,
              head_isSome_of_ne_nil (flatten_cons_ne_nil hB x xs),
              head_isSome_of_ne_nil (flatten_cons_ne_nil hB y ys), Bool.and_self]
          obtain ⟨n, hn, r₁, h₁⟩ := step.run rg x y (flatten xs) (flatten ys)
            width packed frame hwidth
          let packed' := (step.add x y).val.reverse ++ packed
          have hg := guard_eval r₁ step.modulus (flatten xs) (flatten ys) width packed' frame
          obtain ⟨m, hm, r₂, h₂⟩ := ih r₁ ys packed'
          refine ⟨n + 3 + m + 1, ?_, r₂, ?_⟩
          · simp only [List.length_cons]
            rw [show min (xs.length + 1) (ys.length + 1) = min xs.length ys.length + 1 by omega]
            calc
              _ ≤ step.cost + 3 +
                  (min xs.length ys.length * (step.cost + 4) + 1) + 1 := by omega
              _ = _ := by ring
          · have h := Eval.while_true ht (Eval.seq h₁ hg) h₂
            simpa [addLoop, flatten, addWords, rg, packed', List.reverse_append,
              List.append_assoc, Nat.add_assoc] using h

def addWordsTotal : List (Word (B)) → List (Word (B)) →
    List (Word (B))
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (step.add x y) :: addWordsTotal xs ys

theorem addWordsTotal_decompose (xs ys : List (Word (B))) :
    addWordsTotal step xs ys = addWords step xs ys ++ xs.drop ys.length ++ ys.drop xs.length := by
  induction xs generalizing ys with
  | nil => simp [addWordsTotal, addWords]
  | cons x xs ih => cases ys <;> simp [addWordsTotal, addWords, ih]

@[simp] theorem flatten_append {B : ℕ} (xs ys : List (Word B)) :
    flatten (xs ++ ys) = flatten xs ++ flatten ys := by simp [flatten]

theorem addCmd_eval (hB : 0 < B) (regs : Fin 8 → Bool)
    (xs ys : List (Word (B))) (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = B) :
    ∃ n ≤ (xs.length + ys.length + 1) * (step.cost + 15 * B + 20), ∃ regs',
      Eval (addCmd step.cmd) n (ready regs step.modulus (flatten xs) (flatten ys) width [] frame)
        (ready regs' step.modulus (flatten (addWordsTotal step xs ys)) [] width [] frame) := by
  have hg := guard_eval regs step.modulus (flatten xs) (flatten ys) width [] frame
  obtain ⟨n, hn, r₁, hl⟩ := addLoop_eval step hB regs xs ys width [] frame hwidth
  simp only [List.append_nil] at hl
  let left := flatten (xs.drop ys.length)
  let right := flatten (ys.drop xs.length)
  let packed := (flatten (addWords step xs ys)).reverse
  have hf := flush_eval r₁ step.modulus left right width packed frame
  have h := Eval.seq hg (Eval.seq hl hf)
  have hleft : left.length ≤ (xs.length + ys.length) * B := by
    simp only [left, flatten_length, List.length_drop]
    exact Nat.mul_le_mul_right _ (by omega)
  have hright : right.length ≤ (xs.length + ys.length) * B := by
    simp only [right, flatten_length, List.length_drop]
    exact Nat.mul_le_mul_right _ (by omega)
  have hpacked : packed.length ≤ (xs.length + ys.length) * B := by
    simp only [packed, List.length_reverse, flatten_length, addWords_length]
    exact Nat.mul_le_mul_right _ (by omega)
  have hloop : n ≤ (xs.length + ys.length) * (step.cost + 4) + 1 :=
    hn.trans (by gcongr; omega)
  refine ⟨3 + (n + (6 * left.length + 6 * right.length + 3 * packed.length + 9)), ?_,
    readRegs r₁ 0 1 none, ?_⟩
  · nlinarith
  · simpa only [addCmd, List.append_nil, packed, left, right, List.reverse_reverse,
      addWordsTotal_decompose, flatten_append] using h


end SubexponentialSAT.DensePolynomialLoop

end OAI.Algorithms
