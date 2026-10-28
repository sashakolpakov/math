import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.DensePolynomialLoop
import OAI.Algorithms.SubexponentialSAT.SubexpFlatAdd
import OAI.Algorithms.SubexponentialSAT.SubexpDensePolynomial
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# A fixed streaming program for dense polynomial addition

Quartic coefficients are four consecutive fixed-width base words. The loop
uses the actual modular-word addition program and tests the input stacks.
Its instruction table is independent of the array lengths and the width.
-/

namespace SubexponentialSAT.DensePolynomialPrograms

open BitProgram StructuredCalls DensePolynomialLoop
open SubexpLiftRing SubexpQuarticRing

/-- The fixed program calls the same fixed modular-word routine at each step. -/
abbrev addCmd : Cmd 8 20 := DensePolynomialLoop.addCmd SubexpFlatAdd.addOne

abbrev program : Program 8 20 (StructuredCalls.size addCmd + 1) :=
  StructuredCalls.compiled addCmd 8 8

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

/-- The generic loop premise is discharged by the existing actual scalar trace. -/
def wordStep : DensePolynomialLoop.WordStep (baseWidth p μ) where
  cmd := SubexpFlatAdd.addOne
  modulus := M.bits
  add x y := (SubexpPreparedQuartic.wordAdd p μ M x y).1
  cost := SubexpFlatAdd.wordCost (baseWidth p μ)
  run := SubexpFlatAdd.addOne_eval p μ M

def addWordsTotal := DensePolynomialLoop.addWordsTotal (wordStep p μ M)

theorem addCmd_eval (hB : 0 < baseWidth p μ) (regs : Fin 8 → Bool)
    (xs ys : List (Word (baseWidth p μ))) (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p μ) :
    ∃ n ≤ 7000 * (xs.length + ys.length + 1) * (baseWidth p μ + 1) ^ 2, ∃ regs',
      Eval addCmd n (ready regs M.bits (flatten xs) (flatten ys) width [] frame)
        (ready regs' M.bits (flatten (addWordsTotal p μ M xs ys)) [] width [] frame) := by
  obtain ⟨n, hn, rf, hr⟩ := DensePolynomialLoop.addCmd_eval (wordStep p μ M)
    hB regs xs ys width frame hwidth
  have hc : (wordStep p μ M).cost + 15 * baseWidth p μ + 20 ≤
      7000 * (baseWidth p μ + 1) ^ 2 := by
    change SubexpFlatAdd.wordCost (baseWidth p μ) + 15 * baseWidth p μ + 20 ≤ _
    unfold SubexpFlatAdd.wordCost
    ring_nf
    omega
  refine ⟨n, hn.trans ?_, rf, hr⟩
  calc
    _ ≤ (xs.length + ys.length + 1) * (7000 * (baseWidth p μ + 1) ^ 2) :=
      Nat.mul_le_mul_left _ hc
    _ = _ := by ring

/-- Equal-length word arrays represent coordinatewise modular addition. -/
theorem addWordsTotal_values (xs ys : List (Word (baseWidth p μ)))
    (hlen : xs.length = ys.length) :
    (addWordsTotal p μ M xs ys).map (wordValue p μ) =
      List.zipWith (fun x y => wordValue p μ x + wordValue p μ y) xs ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          change wordValue p μ (SubexpPreparedQuartic.wordAdd p μ M x y).1 ::
              (addWordsTotal p μ M xs ys).map (wordValue p μ) =
            (wordValue p μ x + wordValue p μ y) ::
              List.zipWith (fun x y => wordValue p μ x + wordValue p μ y) xs ys
          rw [SubexpPreparedQuartic.wordAdd_correct, ih ys (by simpa using hlen)]

/-- The same fixed loop is a coordinatewise modular vector-addition machine.
Taking μ=1 specializes it to vectors over the prime field. -/
theorem wordVectorAdd_eval (hB : 0 < baseWidth p μ) (regs : Fin 8 → Bool)
    (xs ys : List (Word (baseWidth p μ))) (hlen : xs.length = ys.length)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p μ) :
    ∃ n ≤ 7000 * (xs.length + ys.length + 1) * (baseWidth p μ + 1) ^ 2,
      ∃ (regs' : Fin 8 → Bool) (out : List (Word (baseWidth p μ))),
        out.map (wordValue p μ) =
          List.zipWith (fun x y => wordValue p μ x + wordValue p μ y) xs ys ∧
        Eval addCmd n (ready regs M.bits (flatten xs) (flatten ys) width [] frame)
          (ready regs' M.bits (flatten out) [] width [] frame) := by
  obtain ⟨n, hn, regs', hrun⟩ := addCmd_eval p μ M hB regs xs ys width frame hwidth
  exact ⟨n, hn, regs', addWordsTotal p μ M xs ys,
    addWordsTotal_values p μ M xs ys hlen, hrun⟩

def polynomialWords {B : ℕ} (P : List (Quad (Word B))) : List (Word B) :=
  P.flatMap SubexpFlatAdd.quadWords

def encodePolynomial {B : ℕ} (P : List (Quad (Word B))) : List Bool :=
  flatten (polynomialWords P)

@[simp] theorem polynomialWords_length {B : ℕ} (P : List (Quad (Word B))) :
    (polynomialWords P).length = 4 * P.length := by
  induction P with
  | nil => simp [polynomialWords]
  | cons a P ih =>
      simp only [polynomialWords, List.flatMap_cons, List.length_append] at ⊢
      change 4 + (polynomialWords P).length = 4 * (P.length + 1)
      rw [ih]
      omega

@[simp] theorem encodePolynomial_length {B : ℕ} (P : List (Quad (Word B))) :
    (encodePolynomial P).length = 4 * P.length * B := by
  simp only [encodePolynomial, flatten_length, polynomialWords_length]

theorem addWordsTotal_quad (a b : Quad (Word (baseWidth p μ)))
    (xs ys : List (Word (baseWidth p μ))) :
    addWordsTotal p μ M (SubexpFlatAdd.quadWords a ++ xs) (SubexpFlatAdd.quadWords b ++ ys) =
      SubexpFlatAdd.quadWords (SubexpPreparedQuartic.binaryAdd p μ M a b).1 ++ addWordsTotal p μ M xs ys := rfl

theorem polynomialWords_addProgram
    (ops : SubexpSymbolicCost.RingProgram (Quad (Word (baseWidth p μ))))
    (hadd : ∀ a b, (ops.addRun a b).1 = (SubexpPreparedQuartic.binaryAdd p μ M a b).1)
    (P Q : List (Quad (Word (baseWidth p μ)))) :
    addWordsTotal p μ M (polynomialWords P) (polynomialWords Q) =
      polynomialWords (SubexpDensePolynomial.addProgram ops P Q).1 := by
  induction P generalizing Q with
  | nil => simp [polynomialWords, addWordsTotal, DensePolynomialLoop.addWordsTotal, SubexpDensePolynomial.addProgram]
  | cons a P ih =>
      cases Q with
      | nil => simp [polynomialWords, addWordsTotal, DensePolynomialLoop.addWordsTotal, SubexpFlatAdd.quadWords, SubexpDensePolynomial.addProgram]
      | cons b Q =>
          change addWordsTotal p μ M (SubexpFlatAdd.quadWords a ++ polynomialWords P)
              (SubexpFlatAdd.quadWords b ++ polynomialWords Q) =
            SubexpFlatAdd.quadWords (ops.addRun a b).1 ++
              polynomialWords (SubexpDensePolynomial.addProgram ops P Q).1
          rw [hadd, addWordsTotal_quad, ih]

theorem polynomialAdd_eval (hB : 0 < baseWidth p μ) (regs : Fin 8 → Bool)
    (ops : SubexpSymbolicCost.RingProgram (Quad (Word (baseWidth p μ))))
    (hadd : ∀ a b, (ops.addRun a b).1 = (SubexpPreparedQuartic.binaryAdd p μ M a b).1)
    (P Q : List (Quad (Word (baseWidth p μ)))) (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p μ) :
    ∃ n ≤ 28000 * (P.length + Q.length + 1) * (baseWidth p μ + 1) ^ 2, ∃ regs',
      Eval addCmd n (ready regs M.bits (encodePolynomial P) (encodePolynomial Q) width [] frame)
        (ready regs' M.bits
          (encodePolynomial (SubexpDensePolynomial.addProgram ops P Q).1) [] width [] frame) := by
  obtain ⟨n, hn, rf, hr⟩ := addCmd_eval p μ M hB regs (polynomialWords P) (polynomialWords Q)
    width frame hwidth
  rw [polynomialWords_addProgram p μ M ops hadd] at hr
  refine ⟨n, hn.trans ?_, rf, hr⟩
  simp only [polynomialWords_length]
  apply Nat.mul_le_mul_right ((baseWidth p μ + 1) ^ 2)
  calc
    7000 * (4 * P.length + 4 * Q.length + 1) ≤ 7000 * (4 * (P.length + Q.length + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

theorem polynomialAdd_runs (hB : 0 < baseWidth p μ) (regs : Fin 8 → Bool)
    (ops : SubexpSymbolicCost.RingProgram (Quad (Word (baseWidth p μ))))
    (hadd : ∀ a b, (ops.addRun a b).1 = (SubexpPreparedQuartic.binaryAdd p μ M a b).1)
    (P Q : List (Quad (Word (baseWidth p μ)))) (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p μ) :
    ∃ regs', RunsIn program (30000 * (P.length + Q.length + 1) * (baseWidth p μ + 1) ^ 2)
      ((ready regs M.bits (encodePolynomial P) (encodePolynomial Q) width [] frame).withPC
        (some program.entry))
      ((ready regs' M.bits (encodePolynomial (SubexpDensePolynomial.addProgram ops P Q).1)
        [] width [] frame).withPC none) := by
  obtain ⟨n, hn, rf, hr⟩ := polynomialAdd_eval p μ M hB regs ops hadd P Q width frame hwidth
  refine ⟨rf, n + 1, ?_, StructuredCalls.compiled_halt_trace hr 8 8⟩
  let T := (P.length + Q.length + 1) * (baseWidth p μ + 1) ^ 2
  have hT : 0 < T := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have hn' : n ≤ 28000 * T := by simpa [T, Nat.mul_assoc] using hn
  calc
    n + 1 ≤ 30000 * T := by omega
    _ = _ := by dsimp [T]; ring

theorem polynomialAdd_primitive (hB : 0 < baseWidth p μ) (regs : Fin 8 → Bool)
    (ops : SubexpSymbolicCost.RingProgram (Quad (Word (baseWidth p μ))))
    (hadd : ∀ a b, (ops.addRun a b).1 = (SubexpPreparedQuartic.binaryAdd p μ M a b).1)
    (P Q : List (Quad (Word (baseWidth p μ)))) (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p μ) :
    ∃ regs', Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program *
        (30000 * (P.length + Q.length + 1) * (baseWidth p μ + 1) ^ 2))
      (BitProgram.primitiveCfg program
        ((ready regs M.bits (encodePolynomial P) (encodePolynomial Q) width [] frame).withPC
          (some program.entry)))
      (BitProgram.primitiveCfg program
        ((ready regs' M.bits (encodePolynomial (SubexpDensePolynomial.addProgram ops P Q).1)
          [] width [] frame).withPC none)) := by
  obtain ⟨rf, hr⟩ := polynomialAdd_runs p μ M hB regs ops hadd P Q width frame hwidth
  exact ⟨rf, BitProgram.primitive_execution program hr⟩

/-- Concrete prepared-quartic instantiation, with no callback-refinement premise. -/
theorem preparedPolynomialAdd_primitive (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (t z o : SubexpSymbolicCost.QuarticCode p D) (regs : Fin 8 → Bool)
    (P Q : List (SubexpSymbolicCost.QuarticCode p D))
    (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p (D + 1)) :
    ∃ regs', Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program *
        (30000 * (P.length + Q.length + 1) * (baseWidth p (D + 1) + 1) ^ 2))
      (BitProgram.primitiveCfg program
        ((ready regs M.bits (encodePolynomial P) (encodePolynomial Q) width [] frame).withPC
          (some program.entry)))
      (BitProgram.primitiveCfg program
        ((ready regs' M.bits
          (encodePolynomial (SubexpDensePolynomial.addProgram
            (SubexpSymbolicCost.preparedProgram p D M t z o) P Q).1)
          [] width [] frame).withPC none)) := by
  exact polynomialAdd_primitive p (D + 1) M
    (Nat.mul_pos (Nat.zero_lt_succ D) (Nat.zero_lt_succ _)) regs
    (SubexpSymbolicCost.preparedProgram p D M t z o) (by intros; rfl)
    P Q width frame hwidth

/-- Relocate the fixed addition program into a caller's physical workspace. -/
abbrev callAt {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 20 ↪ Fin s) : Cmd r s :=
  .call (ProgramLinking.liftProgram program registers ports)

private theorem extend_agree {α β γ : Type*} (f : α ↪ β) (values : α → γ)
    (frame : β → γ) (h : ∀ i, frame (f i) = values i) :
    Function.extend f values frame = frame := by
  classical
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [f.injective.extend_apply, h]
  · exact Function.extend_apply' _ _ _ hj

/-- The relocated call changes only its two input/output ports. The complete
bit-level addition trace, including its return instruction, is retained. -/
theorem callAt_eval {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 20 ↪ Fin s)
    (hB : 0 < baseWidth p μ)
    (ops : SubexpSymbolicCost.RingProgram (Quad (Word (baseWidth p μ))))
    (hadd : ∀ a b, (ops.addRun a b).1 = (SubexpPreparedQuartic.binaryAdd p μ M a b).1)
    (P Q : List (Quad (Word (baseWidth p μ)))) (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p μ) (d : State r s)
    (hstore : ∀ i, d.stacks (ports i) =
      (ready (fun _ => false) M.bits (encodePolynomial P) (encodePolynomial Q) width [] frame).stacks i) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool),
      n ≤ 30000 * (P.length + Q.length + 1) * (baseWidth p μ + 1)^2 ∧
      Eval (callAt registers ports) n d
        ⟨Function.extend registers rf d.regs,
          Function.update (Function.update d.stacks (ports 8)
            (encodePolynomial (SubexpDensePolynomial.addProgram ops P Q).1)) (ports 9) []⟩ := by
  let start := ready (fun i => d.regs (registers i)) M.bits
    (encodePolynomial P) (encodePolynomial Q) width [] frame
  obtain ⟨rf, n, hn, ht⟩ := polynomialAdd_runs p μ M hB (fun i => d.regs (registers i))
    ops hadd P Q width frame hwidth
  have hp : projectState registers ports d = start := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      exact hstore i
  have hc := eval_call_from_state program registers ports d registers.injective ports.injective
    (by simpa only [hp] using ht)
  have hout :
      (ready rf M.bits (encodePolynomial (SubexpDensePolynomial.addProgram ops P Q).1)
        [] width [] frame).stacks =
      Function.update (Function.update start.stacks 8
        (encodePolynomial (SubexpDensePolynomial.addProgram ops P Q).1)) 9 [] := by
    funext i
    fin_cases i <;> simp [ready, DensePolynomialLoop.state, stackArray, start,
      Fin.addCases, Fin.coe_ofNat_eq_mod]
  have hi : Function.extend ports start.stacks d.stacks = d.stacks :=
    extend_agree ports start.stacks d.stacks hstore
  have he : embedState registers ports d
      (ready rf M.bits (encodePolynomial (SubexpDensePolynomial.addProgram ops P Q).1)
        [] width [] frame) =
      (⟨Function.extend registers rf d.regs,
        Function.update (Function.update d.stacks (ports 8)
          (encodePolynomial (SubexpDensePolynomial.addProgram ops P Q).1)) (ports 9) []⟩ : State r s) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · change Function.extend ports _ d.stacks = _
      rw [hout, ProgramLinking.extend_update ports.injective,
        ProgramLinking.extend_update ports.injective, hi]
  exact ⟨n, rf, hn, by simpa only [he, callAt] using hc⟩

end SubexponentialSAT.DensePolynomialPrograms

end OAI.Algorithms
