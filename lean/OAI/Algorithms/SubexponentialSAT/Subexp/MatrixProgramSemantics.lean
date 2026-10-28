import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixWordEncoding
import OAI.Algorithms.SubexponentialSAT.CounterPrograms

namespace OAI.Algorithms

/-! Mathematical interpretation of the actual encoded matrix-program outputs. -/

namespace SubexponentialSAT.Subexp.MatrixProgramSemantics

open BinaryArithmetic MatrixProgram MatrixVectorProgram
open scoped BigOperators

theorem canonical_zero_iff (p : ℕ) (bits : List Bool) (hc : BinaryArithmetic.toNat bits < p) :
    BinaryArithmetic.toNat bits = 0 ↔ (BinaryArithmetic.toNat bits : ZMod p) = 0 := by
  rw [← ZMod.val_eq_zero, ZMod.val_natCast_of_lt hc]

theorem rowResult_zero_iff {p B : ℕ} {xs row : List (List Bool)} {result : List Bool}
    (h : RowResult p B xs row result) :
    CounterPrograms.isZero result = true ↔ dotValue p xs row = 0 := by
  rw [CounterPrograms.isZero_eq_true_iff, CounterPrograms.value_eq_toNat,
    canonical_zero_iff p result h.2.1, h.2.2]

theorem dotValue_ofFn (p : ℕ) {N : ℕ} (x y : Fin N → List Bool) :
    dotValue p (List.ofFn x) (List.ofFn y) =
      ∑ i, (BinaryArithmetic.toNat (x i) : ZMod p) * (BinaryArithmetic.toNat (y i) : ZMod p) := by
  induction N with
  | zero => simp [dotValue]
  | succ N ih =>
    simp only [List.ofFn_succ, dotValue, Fin.sum_univ_succ, ih]

theorem encoded_dot (p : ℕ) (code : ZMod p → List Bool)
    (hcode : ∀ a, (BinaryArithmetic.toNat (code a) : ZMod p) = a)
    {N : ℕ} (x y : Fin N → ZMod p) :
    dotValue p (List.ofFn fun i => code (x i)) (List.ofFn fun i => code (y i)) =
      ∑ i, x i * y i := by
  rw [dotValue_ofFn]
  simp only [hcode]

private theorem mapped_of_forall₂ {A B C : Type*} (R : A → B → Prop)
    (f : A → C) (g : B → C) {as : List A} {bs : List B}
    (h : List.Forall₂ R as bs) (hv : ∀ a b, R a b → g b = f a) :
    bs.map g = as.map f := by
  induction h with
  | nil => rfl
  | cons hh ht ih => simp only [List.map_cons, hv _ _ hh, ih]

/-- The program's elementwise result relation is the ordinary matrix-vector
product for any faithful scalar encoding. Canonicality is additionally kept
in the relation for the later executable zero test. -/
theorem matrix_result_values (p B : ℕ) (code : ZMod p → List Bool)
    (hcode : ∀ a, (BinaryArithmetic.toNat (code a) : ZMod p) = a)
    {m N : ℕ} (M : Fin m → Fin N → ZMod p) (x : Fin N → ZMod p)
    (results : List (List Bool))
    (h : List.Forall₂
      (RowResult p B (List.ofFn fun i => code (x i)))
      (List.ofFn fun j => List.ofFn fun i => code (M j i)) results) :
    results.map (fun z => (BinaryArithmetic.toNat z : ZMod p)) =
      List.ofFn (fun j => ∑ i, M j i * x i) := by
  have hm := mapped_of_forall₂
    (RowResult p B (List.ofFn fun i => code (x i)))
    (fun row => dotValue p (List.ofFn fun i => code (x i)) row)
    (fun z => (BinaryArithmetic.toNat z : ZMod p)) h (fun _ _ hz => hz.2.2)
  rw [hm]
  simp only [List.map_ofFn, Function.comp_def, encoded_dot p code hcode]
  congr 1
  funext j
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- With the canonical prime-field code, the output frames contain exactly
the standard words for the mathematical product. This also justifies using
the first product's actual bytes as the second product's input. -/
theorem matrix_result_words (p : ℕ) [Fact p.Prime]
    {m N : ℕ} (M : Fin m → Fin N → ZMod p) (x : Fin N → ZMod p)
    (results : List (List Bool))
    (h : List.Forall₂
      (RowResult p (MatrixWordEncoding.width p)
        (List.ofFn fun i => MatrixWordEncoding.word p (x i)))
      (List.ofFn fun j => List.ofFn fun i => MatrixWordEncoding.word p (M j i)) results) :
    results = List.ofFn (fun j => MatrixWordEncoding.word p (∑ i, M j i * x i)) := by
  have hv := matrix_result_values p (MatrixWordEncoding.width p) (MatrixWordEncoding.word p)
    (MatrixWordEncoding.word_field_value p) M x results h
  have he := MatrixWordEncoding.words_unique p results (List.ofFn fun j => ∑ i, M j i * x i)
    (result_widths h) (result_canonical h) hv
  simpa only [List.map_ofFn, Function.comp_def] using he

end SubexponentialSAT.Subexp.MatrixProgramSemantics

end OAI.Algorithms
