import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScalarProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixCosts

namespace OAI.Algorithms

/-!
# Fixed encoded modular dot products

Vectors are streams of framed, fixed-width little-endian scalar words. The
loop reads the two streams itself and calls the measured multiply-add routine.
Its finite control is independent of the modulus, width, and vector length.
-/

namespace SubexponentialSAT.Subexp.MatrixProgram

open BitProgram StructuredCalls BinaryArithmetic
open MatrixProgramSupport MatrixScalarProgram

abbrev term : Cmd 8 16 :=
  .seq (readWord 10 0 9 (by decide))
    (.seq (readWord 11 1 9 (by decide)) accumulate)

theorem term_eval (regs : Fin 8 → Bool)
    (x y modulus acc left right saved output zero input : List Bool) (B : ℕ)
    (hx : x.length = B) (hy : y.length = B) (ha : acc.length = B)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ n ≤ termBudget B, ∃ regs' result,
      Eval term n
        (state regs [] [] modulus acc (Encoding.frame x ++ left)
          (Encoding.frame y ++ right) saved output zero input)
        (state regs' [] [] modulus result left right saved output zero input) ∧
      result.length = B ∧ BinaryArithmetic.toNat result < BinaryArithmetic.toNat modulus ∧
      (BinaryArithmetic.toNat result : ZMod (BinaryArithmetic.toNat modulus)) =
        (BinaryArithmetic.toNat x : ZMod (BinaryArithmetic.toNat modulus)) * (BinaryArithmetic.toNat y : ZMod (BinaryArithmetic.toNat modulus)) +
          (BinaryArithmetic.toNat acc : ZMod (BinaryArithmetic.toNat modulus)) := by
  obtain ⟨d₁, h₁, hs₁⟩ := readWord_eval (10 : Fin 16) 0 9
    (by decide) (by decide) (by decide)
    (state regs [] [] modulus acc (Encoding.frame x ++ left)
      (Encoding.frame y ++ right) saved output zero input) x left rfl rfl rfl
  have hd₁ : d₁ = state d₁.regs x [] modulus acc left
      (Encoding.frame y ++ right) saved output zero input := by
    apply data_ext <;> try rfl
    rw [hs₁]
    funext j
    fin_cases j <;> simp [ scalarStacks]
  rw [hd₁] at h₁
  obtain ⟨d₂, h₂, hs₂⟩ := readWord_eval (11 : Fin 16) 1 9
    (by decide) (by decide) (by decide)
    (state d₁.regs x [] modulus acc left (Encoding.frame y ++ right) saved output zero input)
    y right rfl rfl rfl
  have hd₂ : d₂ = state d₂.regs x y modulus acc left right saved output zero input := by
    apply data_ext <;> try rfl
    rw [hs₂]
    funext j
    fin_cases j <;> simp [ scalarStacks]
  rw [hd₂] at h₂
  obtain ⟨n₃, hn₃, r₃, result, h₃, hl₃, hc₃, hv₃⟩ :=
    accumulate_eval d₂.regs x y modulus acc left right saved output zero input B
      hx hy ha hml hm hcap
  refine ⟨(9 * B + 7) + ((9 * B + 7) + n₃), ?_, r₃, result, ?_, hl₃, hc₃, hv₃⟩
  · unfold termBudget
    omega
  · simpa only [term, hx, hy] using Eval.seq h₁ (Eval.seq h₂ h₃)

abbrev peekLeft : Cmd 8 16 := .base (.atom (.peek 10 0 1))
abbrev dotBody : Cmd 8 16 := .seq term peekLeft
abbrev dotLoop : Cmd 8 16 := .while 1 dotBody
abbrev dot : Cmd 8 16 := .seq peekLeft dotLoop
def dotProgram := compiled dot 10 8

theorem dotProgram_labels : size dot + 1 = 319 := by decide

def dotValue (p : ℕ) : List (List Bool) → List (List Bool) → ZMod p
  | x :: xs, y :: ys => (BinaryArithmetic.toNat x : ZMod p) * (BinaryArithmetic.toNat y : ZMod p) + dotValue p xs ys
  | _, _ => 0

def ready (regs : Fin 8 → Bool) (modulus acc : List Bool) (xs : List (List Bool))
    (right saved output zero input : List Bool) : MatrixScalarProgram.Data :=
  state (readRegs regs 0 1 (words xs).head?) [] [] modulus acc (words xs)
    right saved output zero input

theorem peekLeft_eval (regs : Fin 8 → Bool) (modulus acc : List Bool)
    (xs : List (List Bool)) (right saved output zero input : List Bool) :
    Eval peekLeft 1 (state regs [] [] modulus acc (words xs) right saved output zero input)
      (ready regs modulus acc xs right saved output zero input) := by
  exact .base (.atom _ _)

theorem ready_nil (regs : Fin 8 → Bool) (modulus acc right saved output zero input : List Bool) :
    (ready regs modulus acc [] right saved output zero input).regs 1 = false := by
  simp [ready, words, state, readRegs]

theorem ready_cons (regs : Fin 8 → Bool) (modulus acc x : List Bool)
    (xs : List (List Bool)) (right saved output zero input : List Bool) :
    (ready regs modulus acc (x :: xs) right saved output zero input).regs 1 = true := by
  cases x <;> simp [ready, words, state, readRegs, Encoding.frame]

theorem dotLoop_eval (xs ys : List (List Bool)) (B : ℕ) (modulus : List Bool)
    (hlen : xs.length = ys.length)
    (hx : ∀ x ∈ xs, x.length = B) (hy : ∀ y ∈ ys, y.length = B)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B)
    (regs : Fin 8 → Bool) (acc right saved output zero input : List Bool)
    (ha : acc.length = B) (hac : BinaryArithmetic.toNat acc < BinaryArithmetic.toNat modulus) :
    ∃ n ≤ xs.length * (termBudget B + 2) + 1, ∃ regs' result,
      Eval dotLoop n (ready regs modulus acc xs (words ys ++ right) saved output zero input)
        (state regs' [] [] modulus result [] right saved output zero input) ∧
      result.length = B ∧ BinaryArithmetic.toNat result < BinaryArithmetic.toNat modulus ∧
      (BinaryArithmetic.toNat result : ZMod (BinaryArithmetic.toNat modulus)) =
        dotValue (BinaryArithmetic.toNat modulus) xs ys + (BinaryArithmetic.toNat acc : ZMod (BinaryArithmetic.toNat modulus)) := by
  induction xs generalizing ys regs acc with
  | nil =>
    have hys : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ys
    refine ⟨1, by simp, (ready regs modulus acc [] right saved output zero input).regs,
      acc, ?_, ha, hac, by simp [dotValue]⟩
    simpa [dotLoop, ready, words, state] using
      (Eval.while_false (test := (1 : Fin 8)) (body := dotBody)
        (ready_nil regs modulus acc right saved output zero input))
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hxt := hx x (by simp)
      have hyt := hy y (by simp)
      let rr := (ready regs modulus acc (x :: xs)
        (words (y :: ys) ++ right) saved output zero input).regs
      obtain ⟨nt, hnt, rt, accNext, het, hlt, hct, hvt⟩ := term_eval rr x y modulus acc
        (words xs) (words ys ++ right) saved output zero input B hxt hyt ha hml hm hcap
      have hterm : Eval term nt
          (ready regs modulus acc (x :: xs) (words (y :: ys) ++ right) saved output zero input)
          (state rt [] [] modulus accNext (words xs) (words ys ++ right) saved output zero input) := by
        simpa [ready, rr, words, List.append_assoc] using het
      have hpeek := peekLeft_eval rt modulus accNext xs (words ys ++ right) saved output zero input
      obtain ⟨nr, hnr, rfinal, result, her, hlr, hcr, hvr⟩ := ih ys (by simpa using hlen)
        (fun z hz => hx z (List.mem_cons_of_mem _ hz))
        (fun z hz => hy z (List.mem_cons_of_mem _ hz)) rt accNext hlt hct
      have he := Eval.while_true
        (ready_cons regs modulus acc x xs (words (y :: ys) ++ right) saved output zero input)
        (Eval.seq hterm hpeek) her
      refine ⟨(nt + 1) + nr + 1, ?_, rfinal, result, he, hlr, hcr, ?_⟩
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · rw [hvr, hvt]
        simp only [dotValue]
        ring

/-- Actual instruction trace for two independently serialized vectors. The
right-stream suffix is preserved, so the same routine consumes one matrix row. -/
theorem dot_trace (xs ys : List (List Bool)) (B : ℕ) (modulus : List Bool)
    (hlen : xs.length = ys.length)
    (hx : ∀ x ∈ xs, x.length = B) (hy : ∀ y ∈ ys, y.length = B)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B)
    (regs : Fin 8 → Bool) (acc right saved output zero input : List Bool)
    (ha : acc.length = B) (hac : BinaryArithmetic.toNat acc < BinaryArithmetic.toNat modulus) :
    ∃ n ≤ xs.length * (termBudget B + 2) + 3, ∃ regs' result,
      Trace dotProgram n
        ((state regs [] [] modulus acc (words xs) (words ys ++ right)
          saved output zero input).withPC (some dotProgram.entry))
        ((state regs' [] [] modulus result [] right saved output zero input).withPC none) ∧
      result.length = B ∧ BinaryArithmetic.toNat result < BinaryArithmetic.toNat modulus ∧
      (BinaryArithmetic.toNat result : ZMod (BinaryArithmetic.toNat modulus)) =
        dotValue (BinaryArithmetic.toNat modulus) xs ys + (BinaryArithmetic.toNat acc : ZMod (BinaryArithmetic.toNat modulus)) := by
  obtain ⟨n, hn, rf, result, he, hl, hc, hv⟩ := dotLoop_eval xs ys B modulus hlen hx hy hml hm
    hcap regs acc right saved output zero input ha hac
  have hp := peekLeft_eval regs modulus acc xs (words ys ++ right) saved output zero input
  exact ⟨(1 + n) + 1, by omega, rf, result,
    compiled_halt_trace (Eval.seq hp he) 10 8, hl, hc, hv⟩

theorem dot_primitive (xs ys : List (List Bool)) (B : ℕ) (modulus : List Bool)
    (hlen : xs.length = ys.length)
    (hx : ∀ x ∈ xs, x.length = B) (hy : ∀ y ∈ ys, y.length = B)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B)
    (regs : Fin 8 → Bool) (acc right saved output zero input : List Bool)
    (ha : acc.length = B) (hac : BinaryArithmetic.toNat acc < BinaryArithmetic.toNat modulus) :
    ∃ regs' result,
      Computation.RunsIn (BitProgram.primitive dotProgram).step
        (BitProgram.primitiveOverhead dotProgram * (xs.length * (termBudget B + 2) + 3))
        (BitProgram.primitiveCfg dotProgram
          ((state regs [] [] modulus acc (words xs) (words ys ++ right)
            saved output zero input).withPC (some dotProgram.entry)))
        (BitProgram.primitiveCfg dotProgram
          ((state regs' [] [] modulus result [] right saved output zero input).withPC none)) ∧
      result.length = B ∧ BinaryArithmetic.toNat result < BinaryArithmetic.toNat modulus ∧
      (BinaryArithmetic.toNat result : ZMod (BinaryArithmetic.toNat modulus)) =
        dotValue (BinaryArithmetic.toNat modulus) xs ys + (BinaryArithmetic.toNat acc : ZMod (BinaryArithmetic.toNat modulus)) := by
  obtain ⟨n, hn, rf, result, ht, hl, hc, hv⟩ := dot_trace xs ys B modulus hlen hx hy hml hm
    hcap regs acc right saved output zero input ha hac
  exact ⟨rf, result, BitProgram.primitive_execution dotProgram ⟨n, hn, ht⟩, hl, hc, hv⟩

end SubexponentialSAT.Subexp.MatrixProgram

end OAI.Algorithms
