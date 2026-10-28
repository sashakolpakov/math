import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchEncoding
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockZeroProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixWordEncoding
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.Subexp.DimensionProgram

namespace OAI.Algorithms

/-!
# Executable predicates for the framed basis-table search

Finite decoding extends the algebraic test to every bit payload. On actual
generated payloads it is exactly the four-zero-test classifier used by the
matrix callback. The proofs retain the generator's actual table, coefficient,
and split representations.
-/

namespace SubexponentialSAT.Subexp.BlockSearchPredicate

open BlockSearch BlockSearchEncoding
open SubexpTupleRefinement

def finiteTest {A : Type*} (values : List A) (encode : A → List Bool)
    (predicate : A → Bool) (bits : List Bool) : Bool :=
  values.any (fun x => decide (encode x = bits) && predicate x)

theorem finiteTest_encoded {A : Type*} (values : List A) (encode : A → List Bool)
    (hinj : Function.Injective encode) (predicate : A → Bool)
    (x : A) (hx : x ∈ values) :
    finiteTest values encode predicate (encode x) = predicate x := by
  apply Bool.eq_iff_iff.mpr
  simp only [finiteTest, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨y, hy, heq, hp⟩
    have hxy : y = x := hinj heq
    simpa only [hxy] using hp
  · intro hp
    exact ⟨x, hx, rfl, hp⟩

section Algebra

variable {K : Type*} [Field K] [DecidableEq K]
variable {m N : ℕ}

def classify (M : Fin m → Fin N → K) (d : Fin (N + 1))
    (C : Fin N → Fin N → K) (x : Fin N → K) : Bool :=
  BlockZeroProgram.classifyResult
    (decide (matrixMap C x = 0)) (decide (x = 0))
    (decide (tailCoefficients d x = 0)) (decide (matrixMap M (matrixMap C x) = 0))

theorem classify_eq_coefficientTest (M : Fin m → Fin N → K) (d : Fin (N + 1))
    (C : Fin N → Fin N → K) (x : Fin N → K) :
    classify M d C x = BlockSearchProgram.coefficientTest M (splitPair d C)
      (headCoefficients d x) (tailCoefficients d x) := by
  have coefficientTest_eq (c : Candidate K N × Candidate K N)
      (a : Fin c.1.1.val → K) (b : Fin c.2.1.val → K) :
      BlockSearchProgram.coefficientTest M c a b =
        BlockZeroProgram.classifyResult
          (decide (combine c.1 a + combine c.2 b = 0))
          (decide (a = 0 ∧ b = 0)) (decide (b = 0))
          (decide (matrixMap M (combine c.1 a + combine c.2 b) = 0)) := by
    unfold BlockSearchProgram.coefficientTest BlockZeroProgram.classifyResult
    by_cases hy : combine c.1 a + combine c.2 b = 0 <;>
      by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
      by_cases hm : matrixMap M (combine c.1 a + combine c.2 b) = 0 <;>
      simp [hy, ha, hb, hm]
  rw [coefficientTest_eq (splitPair d C) (headCoefficients d x)
    (tailCoefficients d x), ← matrixMap_eq_combine d C x]
  unfold classify
  have hcoeff : decide (headCoefficients d x = 0 ∧ tailCoefficients d x = 0) =
      decide (x = 0) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using coefficients_zero_iff d x
  exact congrArg (fun zeroCoefficients =>
    BlockZeroProgram.classifyResult (decide (matrixMap C x = 0)) zeroCoefficients
      (decide (tailCoefficients d x = 0))
      (decide (matrixMap M (matrixMap C x) = 0))) hcoeff.symm

def payloadTest (code : StackEncoding.BlockCode K) (alphabet : List K)
    (M : Fin m → Fin N → K) (d : Fin (N + 1)) (C : Fin N → Fin N → K) :
    List Bool → Bool :=
  finiteTest (QuarticSearch.vectors alphabet N) (encodeTuple code) (classify M d C)

theorem payloadTest_encoded (code : StackEncoding.BlockCode K) (alphabet : List K)
    (hfull : ∀ a, a ∈ alphabet) (M : Fin m → Fin N → K) (d : Fin (N + 1))
    (C : Fin N → Fin N → K) (x : Fin N → K) :
    payloadTest code alphabet M d C (encodeTuple code x) =
      BlockSearchProgram.coefficientTest M (splitPair d C)
        (headCoefficients d x) (tailCoefficients d x) := by
  rw [payloadTest, finiteTest_encoded _ _ (encodeTuple_injective code N) _ x
    (QuarticSearch.mem_vectors alphabet hfull N x)]
  exact classify_eq_coefficientTest M d C x

omit [Field K] [DecidableEq K] in
theorem encodeTuple_split (code : StackEncoding.BlockCode K) (d : Fin (N + 1))
    (x : Fin N → K) :
    encodeTuple code x = encodeTuple code (headCoefficients d x) ++
      encodeTuple code (tailCoefficients d x) := by
  have hN : d.val + (N - d.val) = N := by have := d.isLt; omega
  unfold encodeTuple
  rw [List.ofFn_congr hN.symm x, List.ofFn_add, StackEncoding.encodeDataStack_append]
  rfl

theorem payloadTest_pair (code : StackEncoding.BlockCode K) (alphabet : List K)
    (hfull : ∀ a, a ∈ alphabet) (M : Fin m → Fin N → K) (d : Fin (N + 1))
    (C : Fin N → Fin N → K) (a : Fin d.val → K) (b : Fin (N - d.val) → K) :
    payloadTest code alphabet M d C (encodeTuple code a ++ encodeTuple code b) =
      BlockSearchProgram.coefficientTest M (splitPair d C) a b := by
  have h := payloadTest_encoded code alphabet hfull M d C (joinCoefficients d a b)
  rw [encodeTuple_split code d, headCoefficients_join, tailCoefficients_join] at h
  exact h

theorem all_payloads_iff_goodPair (code : StackEncoding.BlockCode K) (alphabet : List K)
    (hfull : ∀ a, a ∈ alphabet) (M : Fin m → Fin N → K) (d : Fin (N + 1))
    (C : Fin N → Fin N → K) :
    (BlockSearchProgram.coefficientRecords code alphabet (splitPair d C)).all
      (payloadTest code alphabet M d C) = true ↔ GoodPair M (splitPair d C) := by
  apply BlockSearchProgram.coefficientRecords_all_iff_goodPair code alphabet hfull M
    (splitPair d C) (splitPair_dimensions_add d C)
  exact payloadTest_pair code alphabet hfull M d C

def splitCode (d : Fin (N + 1)) : List Bool := List.replicate d.val true

theorem splitCode_injective : Function.Injective (splitCode (N := N)) := by
  intro d e h
  apply Fin.ext
  have hl := congrArg List.length h
  simpa only [splitCode, List.length_replicate] using hl

def encodedTest (code : StackEncoding.BlockCode K) (alphabet : List K)
    (M : Fin m → Fin N → K) (tableBits splitBits coefficientBits : List Bool) : Bool :=
  finiteTest (QuarticSearch.vectors alphabet (N * N)) (encodeTuple code)
    (fun flat => finiteTest (List.finRange (N + 1)) splitCode
      (fun d => payloadTest code alphabet M d (unflattenTable flat) coefficientBits) splitBits)
    tableBits

theorem encodedTest_encoded (code : StackEncoding.BlockCode K) (alphabet : List K)
    (hfull : ∀ a, a ∈ alphabet) (M : Fin m → Fin N → K) (d : Fin (N + 1))
    (C : Fin N → Fin N → K) (bits : List Bool) :
    encodedTest code alphabet M (encodeTuple code (flattenTable C)) (splitCode d) bits =
      payloadTest code alphabet M d C bits := by
  unfold encodedTest
  rw [finiteTest_encoded _ _ (encodeTuple_injective code (N * N)) _ (flattenTable C)
    (QuarticSearch.mem_vectors alphabet hfull (N * N) (flattenTable C))]
  rw [finiteTest_encoded _ _ splitCode_injective _ d (by simp)]
  simp only [unflattenTable_flattenTable]

theorem encodedTest_coefficient (code : StackEncoding.BlockCode K) (alphabet : List K)
    (hfull : ∀ a, a ∈ alphabet) (M : Fin m → Fin N → K) (d : Fin (N + 1))
    (C : Fin N → Fin N → K) (x : Fin N → K) :
    encodedTest code alphabet M (encodeTuple code (flattenTable C)) (splitCode d)
      (encodeTuple code x) = BlockSearchProgram.coefficientTest M (splitPair d C)
        (headCoefficients d x) (tailCoefficients d x) := by
  rw [encodedTest_encoded code alphabet hfull, payloadTest_encoded code alphabet hfull]

theorem all_encoded_iff_goodPair (code : StackEncoding.BlockCode K) (alphabet : List K)
    (hfull : ∀ a, a ∈ alphabet) (M : Fin m → Fin N → K) (d : Fin (N + 1))
    (C : Fin N → Fin N → K) :
    (BlockSearchProgram.coefficientRecords code alphabet (splitPair d C)).all
      (encodedTest code alphabet M (encodeTuple code (flattenTable C)) (splitCode d)) = true ↔
        GoodPair M (splitPair d C) := by
  have heq : encodedTest code alphabet M (encodeTuple code (flattenTable C)) (splitCode d) =
      payloadTest code alphabet M d C := by
    funext bits
    exact encodedTest_encoded code alphabet hfull M d C bits
  rw [heq]
  exact all_payloads_iff_goodPair code alphabet hfull M d C

theorem exists_encoded_success (code : StackEncoding.BlockCode K) (alphabet : List K)
    (hfull : ∀ a, a ∈ alphabet) (M : Fin m → Fin N → K) :
    ∃ (d : Fin (N + 1)) (C : Fin N → Fin N → K),
      encodeTuple code (flattenTable C) ∈
        TupleProgram.powerRows (alphabet.map code.block) (N * N) [[]] ∧
      splitCode d ∈ DimensionProgram.dimensionRows 0 N ∧
      (BlockSearchProgram.coefficientRecords code alphabet (splitPair d C)).all
        (encodedTest code alphabet M (encodeTuple code (flattenTable C)) (splitCode d)) = true := by
  obtain ⟨d, C, hgood⟩ := exists_good_splitPair M
  refine ⟨d, C, encodeTuple_mem_powerRows code alphabet hfull (N * N) (flattenTable C), ?_, ?_⟩
  · exact (DimensionProgram.mem_dimensionRows 0 N d.val).mpr ⟨Nat.zero_le _, by have := d.isLt; omega⟩
  · exact (all_encoded_iff_goodPair code alphabet hfull M d C).mpr hgood

omit [Field K] [DecidableEq K] in
theorem encodeFramed_list (code : StackEncoding.BlockCode K) (xs : List K) :
    StackEncoding.encodeDataStack (BlockSearchProgram.framedCode code) xs =
      MatrixProgramSupport.words (xs.map code.block) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change Encoding.frame (code.block x) ++
        StackEncoding.encodeDataStack (BlockSearchProgram.framedCode code) xs =
          Encoding.frame (code.block x) ++ MatrixProgramSupport.words (xs.map code.block)
      rw [ih]

end Algebra

section Prime

variable (p : ℕ) [Fact p.Prime]

def scalarCode : StackEncoding.BlockCode (ZMod p) :=
  BlockSearchProgram.framedCode (MatrixWordEncoding.code p)

theorem encoded_vector_eq_words {N : ℕ} (x : Fin N → ZMod p) :
    encodeTuple (scalarCode p) x =
      MatrixProgramSupport.words (List.ofFn fun i => MatrixWordEncoding.word p (x i)) := by
  rw [encodeTuple, scalarCode, encodeFramed_list, List.map_ofFn]
  rfl

theorem encoded_table_eq_flatten_words {N : ℕ} (C : Fin N → Fin N → ZMod p) :
    encodeTuple (scalarCode p) (flattenTable C) =
      MatrixProgramSupport.words
        ((List.ofFn fun row => List.ofFn fun col => MatrixWordEncoding.word p (C row col)).flatten) := by
  rw [encoded_vector_eq_words]
  apply congrArg MatrixProgramSupport.words
  change tableEntries (fun row col => MatrixWordEncoding.word p (C row col)) = _
  exact tableEntries_eq_flatten_rows (fun row col => MatrixWordEncoding.word p (C row col))

theorem words_split {N : ℕ} (d : Fin (N + 1)) (x : Fin N → ZMod p) :
    MatrixProgramSupport.words (List.ofFn fun i => MatrixWordEncoding.word p (x i)) =
      MatrixProgramSupport.words
        (List.ofFn fun i => MatrixWordEncoding.word p (headCoefficients d x i)) ++
      MatrixProgramSupport.words
        (List.ofFn fun i => MatrixWordEncoding.word p (tailCoefficients d x i)) := by
  rw [← encoded_vector_eq_words p x, encodeTuple_split (scalarCode p) d x,
    encoded_vector_eq_words p (headCoefficients d x),
    encoded_vector_eq_words p (tailCoefficients d x)]

def test (alphabet : List (ZMod p)) {m N : ℕ} (M : Fin m → Fin N → ZMod p) :
    List Bool → List Bool → List Bool → Bool := encodedTest (scalarCode p) alphabet M

theorem test_on_words (alphabet : List (ZMod p)) (hfull : ∀ a, a ∈ alphabet)
    {m N : ℕ} (M : Fin m → Fin N → ZMod p) (d : Fin (N + 1))
    (C : Fin N → Fin N → ZMod p) (x : Fin N → ZMod p) :
    test p alphabet M (encodeTuple (scalarCode p) (flattenTable C)) (splitCode d)
      (MatrixProgramSupport.words (List.ofFn fun i => MatrixWordEncoding.word p (x i))) =
      BlockSearchProgram.coefficientTest M (splitPair d C)
        (headCoefficients d x) (tailCoefficients d x) := by
  rw [← encoded_vector_eq_words p x]
  exact encodedTest_coefficient (scalarCode p) alphabet hfull M d C x

theorem test_on_flattened_rows (alphabet : List (ZMod p)) (hfull : ∀ a, a ∈ alphabet)
    {m N : ℕ} (M : Fin m → Fin N → ZMod p) (d : Fin (N + 1))
    (C : Fin N → Fin N → ZMod p) (x : Fin N → ZMod p) :
    test p alphabet M
      (MatrixProgramSupport.words
        ((List.ofFn fun row => List.ofFn fun col => MatrixWordEncoding.word p (C row col)).flatten))
      (splitCode d)
      (MatrixProgramSupport.words (List.ofFn fun i => MatrixWordEncoding.word p (x i))) =
      BlockSearchProgram.coefficientTest M (splitPair d C)
        (headCoefficients d x) (tailCoefficients d x) := by
  rw [← encoded_table_eq_flatten_words p C]
  exact test_on_words p alphabet hfull M d C x

end Prime

end SubexponentialSAT.Subexp.BlockSearchPredicate

end OAI.Algorithms
