import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.DensePolynomialPrograms
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramSerialization

namespace OAI.Algorithms

/-! Native addition of dense polynomial arrays whose coefficients have an
arbitrary runtime extension degree. The fixed scanner visits base words;
there is no quartet assumption and no generated instruction table. -/

namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.DensePolynomialLoop
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev Coeff (B d : ℕ) := RingProgram.Code (Word B) d

def words {B d : ℕ} (P : List (Coeff B d)) : List (Word B) :=
  P.flatMap List.ofFn

def encode {B d : ℕ} (P : List (Coeff B d)) : List Bool :=
  (P.map RingProgram.flat).flatten

@[simp] theorem words_length {B d : ℕ} (P : List (Coeff B d)) :
    (words P).length = P.length * d := by
  induction P with
  | nil => simp [words]
  | cons a P ih => simp [words, Nat.add_mul, Nat.add_comm]

@[simp] theorem encode_cons {B d : ℕ} (a : Coeff B d) (P : List (Coeff B d)) :
    encode (a :: P) = RingProgram.flat a ++ encode P := rfl

@[simp] theorem encode_nil {B d : ℕ} : encode ([] : List (Coeff B d)) = [] := rfl

theorem encode_eq_flatten_words {B d : ℕ} (P : List (Coeff B d)) :
    encode P = flatten (words P) := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      simp [encode, words, flatten, RingProgram.flat, List.map_ofFn, Function.comp_def,
        show (P.map RingProgram.flat).flatten = flatten (words P) from ih]

@[simp] theorem encode_length {B d : ℕ} (P : List (Coeff B d)) :
    (encode P).length = P.length * (d * B) := by
  rw [encode_eq_flatten_words, flatten_length, words_length, Nat.mul_assoc]

private theorem addWords_append {B : ℕ} (step : WordStep B)
    (xs ys as bs : List (Word B)) (hlen : xs.length = ys.length) :
    addWordsTotal step (xs ++ as) (ys ++ bs) =
      List.zipWith step.add xs ys ++ addWordsTotal step as bs := by
  induction xs generalizing ys with
  | nil =>
      have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
      subst ys
      rfl
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          simp only [List.cons_append, addWordsTotal, List.zipWith_cons_cons]
          rw [ih ys (by simpa using hlen)]

private theorem zipWith_ofFn {A B C : Type*} (f : A → B → C) {d : ℕ}
    (a : Fin d → A) (b : Fin d → B) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => f (a i) (b i)) := by
  induction d with
  | zero => simp
  | succ d ih =>
      simp only [List.ofFn_succ, List.zipWith_cons_cons]
      rw [ih]

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)

private theorem words_add_block {d : ℕ}
    (a b : Coeff (baseWidth p t) d) (xs ys : List (Word (baseWidth p t))) :
    SubexponentialSAT.DensePolynomialPrograms.addWordsTotal p t M
        (List.ofFn a ++ xs) (List.ofFn b ++ ys) =
      List.ofFn (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1 ++
        SubexponentialSAT.DensePolynomialPrograms.addWordsTotal p t M xs ys := by
  rw [SubexponentialSAT.DensePolynomialPrograms.addWordsTotal,
    addWords_append _ _ _ _ _ (by simp), zipWith_ofFn]
  simp only [SubexponentialSAT.DensePolynomialPrograms.wordStep, RingProgram.addRun,
    RingProgram.tabulateRun_eq, RingProgram.scalarProgram]

private theorem addWordsTotal_nil_right {B : ℕ} (step : WordStep B) (xs : List (Word B)) :
    addWordsTotal step xs [] = xs := by cases xs <;> rfl

theorem words_add {d : ℕ}
    (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) d))
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (P Q : List (Coeff (baseWidth p t) d)) :
    SubexponentialSAT.DensePolynomialPrograms.addWordsTotal p t M (words P) (words Q) =
      words (SubexponentialSAT.SubexpDensePolynomial.addProgram ops P Q).1 := by
  induction P generalizing Q with
  | nil => simp [words, SubexponentialSAT.DensePolynomialPrograms.addWordsTotal,
      addWordsTotal, SubexponentialSAT.SubexpDensePolynomial.addProgram]
  | cons a P ih =>
      cases Q with
      | nil => simp only [SubexponentialSAT.SubexpDensePolynomial.addProgram, words, List.flatMap_nil,
          SubexponentialSAT.DensePolynomialPrograms.addWordsTotal, addWordsTotal_nil_right]
      | cons b Q =>
          simp only [words, List.flatMap_cons, SubexponentialSAT.SubexpDensePolynomial.addProgram]
          change SubexponentialSAT.DensePolynomialPrograms.addWordsTotal p t M
            (List.ofFn a ++ words P) (List.ofFn b ++ words Q) =
            List.ofFn (ops.addRun a b).1 ++ words (SubexponentialSAT.SubexpDensePolynomial.addProgram ops P Q).1
          rw [words_add_block p t M cache, hadd, ih]

/-- This code is the same fixed scalar-word scanner for every extension degree,
polynomial length, modulus, and coefficient width. -/
abbrev addCmd : Cmd 8 20 := SubexponentialSAT.DensePolynomialPrograms.addCmd

abbrev addProgram : Program 8 20 (size addCmd + 1) := compiled addCmd 8 8

theorem add_eval {d : ℕ} (hB : 0 < baseWidth p t) (regs : Fin 8 → Bool)
    (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) d))
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (P Q : List (Coeff (baseWidth p t) d)) (width : List Bool)
    (frame : Fin 6 → List Bool) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ 7000 * (d * (P.length + Q.length) + 1) * (baseWidth p t + 1)^2,
      ∃ regs', Eval addCmd n
        (ready regs M.bits (encode P) (encode Q) width [] frame)
        (ready regs' M.bits (encode (SubexponentialSAT.SubexpDensePolynomial.addProgram ops P Q).1)
          [] width [] frame) := by
  obtain ⟨n, hn, rf, he⟩ := SubexponentialSAT.DensePolynomialPrograms.addCmd_eval p t M hB regs
    (words P) (words Q) width frame hwidth
  rw [words_add p t M cache ops hadd P Q] at he
  refine ⟨n, ?_, rf, ?_⟩
  · simpa only [words_length, show P.length * d + Q.length * d = d * (P.length + Q.length) by ring] using hn
  · simpa only [addCmd, encode_eq_flatten_words] using he

theorem add_trace {d : ℕ} (hB : 0 < baseWidth p t) (regs : Fin 8 → Bool)
    (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) d))
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (P Q : List (Coeff (baseWidth p t) d)) (width : List Bool)
    (frame : Fin 6 → List Bool) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ 7000 * (d * (P.length + Q.length) + 1) * (baseWidth p t + 1)^2 + 1,
      ∃ regs', Trace addProgram n
        ((ready regs M.bits (encode P) (encode Q) width [] frame).withPC (some addProgram.entry))
        ((ready regs' M.bits (encode (SubexponentialSAT.SubexpDensePolynomial.addProgram ops P Q).1)
          [] width [] frame).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := add_eval p t M cache hB regs ops hadd P Q width frame hwidth
  exact ⟨n + 1, by omega, rf, compiled_halt_trace he 8 8⟩

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
