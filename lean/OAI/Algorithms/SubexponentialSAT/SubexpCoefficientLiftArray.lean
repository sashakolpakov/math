import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFlatLift

namespace OAI.Algorithms

/-!+# A fixed coefficientwise lift of a complete polynomial row

The input on stack 8 is a concatenation of four-word coefficients. The
machine tests that tape for emptiness and applies the already checked word
lift. Stack 9 receives the reversal of the complete target tape, as expected
by the Taylor row program. No row-length counter is an input.+
The source modulus (5), source width (10), target width (11), and six caller
frame stacks are preserved. All other work stacks are empty on return.
-/

namespace SubexponentialSAT.SubexpCoefficientLiftArray

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

abbrev Data := State 8 20

abbrev guard : Cmd 8 20 := .base (.atom (.peek 8 0 7))

def guardRegs (regs : Fin 8 → Bool) (input : List Bool) : Fin 8 → Bool :=
  readRegs regs 0 7 input.head?

@[simp] theorem guardRegs_test (regs : Fin 8 → Bool) (input : List Bool) :
    guardRegs regs input 7 = input.head?.isSome := by
  simp [guardRegs, readRegs]

theorem guard_eval (regs : Fin 8 → Bool)
    (modulus input packed sw tw : List Bool) (frame : Fin 6 → List Bool) :
    Eval guard 1 (SubexpFlatLift.ready regs modulus input packed sw tw frame)
      (SubexpFlatLift.ready (guardRegs regs input) modulus input packed sw tw frame) := by
  exact Eval.base (StructuredProgram.Eval.atom (.peek 8 0 7)
    (SubexpFlatLift.ready regs modulus input packed sw tw frame))

abbrev loop : Cmd 8 20 := .while 7 (.seq SubexpFlatLift.liftOne guard)

abbrev command : Cmd 8 20 := .seq guard loop

abbrev program : Program 8 20 (size command + 1) := compiled command 8 9

private theorem flatten_append {B : ℕ} (xs ys : List (Word B)) :
    SubexpFlatLift.flatten (xs ++ ys) =
      SubexpFlatLift.flatten xs ++ SubexpFlatLift.flatten ys := by
  simp [SubexpFlatLift.flatten]

private theorem flatten_cons_nonempty {B : ℕ} (hB : 0 < B)
    (x : Word B) (xs : List (Word B)) :
    (SubexpFlatLift.flatten (x :: xs)).head?.isSome = true := by
  have hx : x.val ≠ [] := by
    intro he
    have hlen := x.property
    rw [he] at hlen
    simp only [List.length_nil] at hlen
    omega
  cases he : x.val with
  | nil => exact (hx he).elim
  | cons bit rest => simp [SubexpFlatLift.flatten, he]

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)

theorem loop_eval (hμ : 0 < μ) (regs : Fin 8 → Bool)
    (xs : List (Word (baseWidth p 1))) (packed sw tw : List Bool)
    (frame : Fin 6 → List Bool)
    (hb : sw.length = baseWidth p 1) (hB : tw.length = baseWidth p μ) :
    ∃ n ≤ xs.length *
        (SubexpFlatLift.wordCost (baseWidth p 1) (baseWidth p μ) M.bits.length + 2) + 1,
      ∃ rf, Eval loop n
        (SubexpFlatLift.ready (guardRegs regs (SubexpFlatLift.flatten xs)) M.bits
          (SubexpFlatLift.flatten xs) packed sw tw frame)
        (SubexpFlatLift.ready rf M.bits []
          ((SubexpFlatLift.flatten (SubexpFlatLift.liftedWords p μ M xs)).reverse ++ packed)
          sw tw frame) := by
  induction xs generalizing regs packed with
  | nil =>
      refine ⟨1, by simp, guardRegs regs [], ?_⟩
      simpa [loop, SubexpFlatLift.flatten, SubexpFlatLift.liftedWords] using
        (Eval.while_false (test := (7 : Fin 8))
          (body := .seq SubexpFlatLift.liftOne guard)
          (a := SubexpFlatLift.ready (guardRegs regs []) M.bits [] packed sw tw frame)
          (by simp [SubexpFlatLift.ready, SubexpFlatLift.state]))
  | cons x xs ih =>
      let rg := guardRegs regs (SubexpFlatLift.flatten (x :: xs))
      have hbpos : 0 < baseWidth p 1 := by
        simp [baseWidth]
      have ht : (SubexpFlatLift.ready rg M.bits
          (SubexpFlatLift.flatten (x :: xs)) packed sw tw frame).regs 7 = true := by
        simp only [SubexpFlatLift.ready, SubexpFlatLift.state, rg, guardRegs_test,
          flatten_cons_nonempty hbpos x xs]
      obtain ⟨n, hn, r₁, h₁⟩ := SubexpFlatLift.liftOne_eval p μ M hμ rg x
        (SubexpFlatLift.flatten xs) packed sw tw frame hb hB
      let packed' := (SubexpWordLift.liftWordRun p μ M x).1.val.reverse ++ packed
      have hg := guard_eval r₁ M.bits (SubexpFlatLift.flatten xs) packed' sw tw frame
      obtain ⟨m, hm, rf, h₂⟩ := ih r₁ packed'
      refine ⟨n + 1 + m + 1, ?_, rf, ?_⟩
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · have h := Eval.while_true ht (Eval.seq h₁ hg) h₂
        simpa [loop, rg, packed', SubexpFlatLift.flatten, SubexpFlatLift.liftedWords,
          List.reverse_append, List.append_assoc, Nat.add_assoc] using h

theorem command_eval (hμ : 0 < μ) (regs : Fin 8 → Bool)
    (xs : List (Word (baseWidth p 1))) (sw tw : List Bool)
    (frame : Fin 6 → List Bool)
    (hb : sw.length = baseWidth p 1) (hB : tw.length = baseWidth p μ) :
    ∃ n ≤ xs.length *
        (SubexpFlatLift.wordCost (baseWidth p 1) (baseWidth p μ) M.bits.length + 2) + 2,
      ∃ rf, Eval command n
        (SubexpFlatLift.ready regs M.bits (SubexpFlatLift.flatten xs) [] sw tw frame)
        (SubexpFlatLift.ready rf M.bits []
          (SubexpFlatLift.flatten (SubexpFlatLift.liftedWords p μ M xs)).reverse sw tw frame) := by
  have hg := guard_eval regs M.bits (SubexpFlatLift.flatten xs) [] sw tw frame
  obtain ⟨n, hn, rf, hr⟩ := loop_eval p μ M hμ regs xs [] sw tw frame hb hB
  refine ⟨1+n, by omega, rf, ?_⟩
  simpa only [command, List.append_nil] using Eval.seq hg hr

def encodeArray {B : ℕ} (P : List (Quad (Word B))) : List Bool :=
  (P.map SubexpFlatLift.encode).flatten

def wordsOf {B : ℕ} (P : List (Quad (Word B))) : List (Word B) :=
  P.flatMap SubexpFlatLift.quadWords

@[simp] theorem wordsOf_length {B : ℕ} (P : List (Quad (Word B))) :
    (wordsOf P).length = 4 * P.length := by
  induction P with
  | nil => simp [wordsOf]
  | cons a P ih =>
      simp only [wordsOf, List.flatMap_cons, List.length_append,
        SubexpFlatLift.quadWords, List.length_cons, List.length_nil] at *
      omega

theorem flatten_wordsOf {B : ℕ} (P : List (Quad (Word B))) :
    SubexpFlatLift.flatten (wordsOf P) = encodeArray P := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      simpa only [wordsOf, List.flatMap_cons, flatten_append, encodeArray,
        List.map_cons, List.flatten_cons, SubexpFlatLift.encode] using
        congrArg (SubexpFlatLift.encode a ++ ·) ih

def liftedArray (P : List (Quad (Word (baseWidth p 1)))) :
    List (Quad (Word (baseWidth p μ))) :=
  P.map (fun a => (SubexpWordLift.liftQuadRun p μ M a).1)

omit [Fact p.Prime] in
theorem flatten_liftedWords (P : List (Quad (Word (baseWidth p 1)))) :
    SubexpFlatLift.flatten (SubexpFlatLift.liftedWords p μ M (wordsOf P)) =
      encodeArray (liftedArray p μ M P) := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      have hquad : SubexpFlatLift.liftedWords p μ M (SubexpFlatLift.quadWords a) =
          SubexpFlatLift.quadWords (SubexpWordLift.liftQuadRun p μ M a).1 := rfl
      have happend (xs ys : List (Word (baseWidth p 1))) :
          SubexpFlatLift.liftedWords p μ M (xs ++ ys) =
            SubexpFlatLift.liftedWords p μ M xs ++ SubexpFlatLift.liftedWords p μ M ys := by
        simp [SubexpFlatLift.liftedWords]
      change SubexpFlatLift.flatten (SubexpFlatLift.liftedWords p μ M
        (SubexpFlatLift.quadWords a ++ wordsOf P)) = _
      rw [happend, flatten_append, hquad, ih]
      rfl

theorem program_runs (hμ : 0 < μ) (regs : Fin 8 → Bool)
    (P : List (Quad (Word (baseWidth p 1)))) (sw tw : List Bool)
    (frame : Fin 6 → List Bool)
    (hb : sw.length = baseWidth p 1) (hB : tw.length = baseWidth p μ) :
    ∃ rf, RunsIn program
      (3000 * (P.length + 1) * (baseWidth p 1 + baseWidth p μ + 2)^2)
      ((SubexpFlatLift.ready regs M.bits (encodeArray P) [] sw tw frame).withPC
        (some program.entry))
      ((SubexpFlatLift.ready rf M.bits [] (encodeArray (liftedArray p μ M P)).reverse
        sw tw frame).withPC none) := by
  obtain ⟨n, hn, rf, hr⟩ := command_eval p μ M hμ regs (wordsOf P) sw tw frame hb hB
  rw [flatten_wordsOf, flatten_liftedWords] at hr
  refine ⟨rf, n+1, ?_, compiled_halt_trace hr 8 9⟩
  rw [wordsOf_length] at hn
  let S := baseWidth p 1 + baseWidth p μ + 2
  have hsq : S ≤ S^2 := by
    simpa only [pow_two, Nat.mul_one] using
      Nat.mul_le_mul_left S (show 1 ≤ S by dsimp [S]; omega)
  have hc := SubexpWordLiftMachine.runtimeBound_uniform
    (baseWidth p 1) (baseWidth p μ) M.bits.length M.length_le
  have hword : SubexpFlatLift.wordCost (baseWidth p 1) (baseWidth p μ) M.bits.length + 3 ≤
      600 * S^2 := by
    unfold SubexpFlatLift.wordCost
    dsimp [S] at hsq ⊢
    omega
  calc
    n + 1 ≤ (4 * P.length + 1) *
        (SubexpFlatLift.wordCost (baseWidth p 1) (baseWidth p μ) M.bits.length + 3) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul] at hn ⊢
      omega
    _ ≤ (4 * P.length + 1) * (600 * S^2) := Nat.mul_le_mul_left _ hword
    _ ≤ (5 * (P.length + 1)) * (600 * S^2) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = 3000 * (P.length + 1) * S^2 := by ring

theorem program_primitive (hμ : 0 < μ) (regs : Fin 8 → Bool)
    (P : List (Quad (Word (baseWidth p 1)))) (sw tw : List Bool)
    (frame : Fin 6 → List Bool)
    (hb : sw.length = baseWidth p 1) (hB : tw.length = baseWidth p μ) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program *
        (3000 * (P.length + 1) * (baseWidth p 1 + baseWidth p μ + 2)^2))
      (primitiveCfg program
        ((SubexpFlatLift.ready regs M.bits (encodeArray P) [] sw tw frame).withPC
          (some program.entry)))
      (primitiveCfg program
        ((SubexpFlatLift.ready rf M.bits [] (encodeArray (liftedArray p μ M P)).reverse
          sw tw frame).withPC none)) := by
  obtain ⟨rf, hr⟩ := program_runs p μ M hμ regs P sw tw frame hb hB
  exact ⟨rf, primitive_execution _ hr⟩

end SubexponentialSAT.SubexpCoefficientLiftArray

end OAI.Algorithms
