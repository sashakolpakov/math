import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLeafData
import OAI.Algorithms.SubexponentialSAT.SubexpH0Finalize
import OAI.Algorithms.SubexponentialSAT.SubexpEmptyClauseGuard

namespace OAI.Algorithms

/-!
# Typed sparse-leaf semantics at the actual finalizer boundary

The byte test below is a finite reference computation used only in the
correctness statement. The fast callback obtains its answer from the actual
moment, reconstruction, and finalizer programs. No execution or fast bound
for this reference decoder/search is asserted.
-/

namespace SubexponentialSAT.SubexpLeafSemantics

open StructuredCalls SubexpMainProgram SubexpQuarticRing SubexpLayoutSpec

abbrev Leaf (n : ℕ) := SubexpLeafData.Leaf n

def literalBytes {n : ℕ} (l : SAT.Literal (Fin n)) : List Bool :=
  Encoding.encodeNat (Encoding.literalCode l)

def decodeLiteral (n : ℕ) (bits : List Bool) : Option (SAT.Literal (Fin n)) :=
  match Encoding.readNat bits with
  | some (code, []) =>
      if h : code / 2 < n then some ⟨⟨code / 2, h⟩, decide (code % 2 = 1)⟩ else none
  | _ => none

theorem literalCode_div_two {n : ℕ} (l : SAT.Literal (Fin n)) :
    Encoding.literalCode l / 2 = l.variable.val := by
  rcases l with ⟨v, sign⟩
  cases sign <;> simp [Encoding.literalCode] ; omega

theorem literalCode_polarity {n : ℕ} (l : SAT.Literal (Fin n)) :
    decide (Encoding.literalCode l % 2 = 1) = l.positive := by
  rcases l with ⟨v, sign⟩
  cases sign <;> simp [Encoding.literalCode]

@[simp] theorem decodeLiteral_literalBytes {n : ℕ} (l : SAT.Literal (Fin n)) :
    decodeLiteral n (literalBytes l) = some l := by
  simp only [decodeLiteral, literalBytes, Encoding.readNat_encodeNat,
    literalCode_div_two, literalCode_polarity, l.variable.isLt, dite_eq_left]

def decodeRecords {α : Type*} (decode : List Bool → Option α)
    (bits : List Bool) : Option (List α) :=
  match ProgramEncoding.readRecords bits with
  | some (records, []) => records.mapM decode
  | _ => none

theorem decodeRecords_encode {α : Type*} (encode : α → List Bool)
    (decode : List Bool → Option α) (h : ∀ a, decode (encode a) = some a)
    (xs : List α) :
    decodeRecords decode (Encoding.encodeList encode xs) = some xs := by
  have hm : (xs.map encode).mapM decode = some xs := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp [h a, ih]
  have he := ExecSparsifyEncoding.encodeList_map encode id xs
  change ProgramEncoding.encodeRecords (xs.map encode) = Encoding.encodeList encode xs at he
  rw [← he]
  simpa only [decodeRecords, ProgramEncoding.readRecords_encodeRecords] using hm

def clauseBytes {n : ℕ} (C : List (SAT.Literal (Fin n))) : List Bool :=
  Encoding.encodeList literalBytes C

def decodeClause (n : ℕ) : List Bool → Option (List (SAT.Literal (Fin n))) :=
  decodeRecords (decodeLiteral n)

@[simp] theorem decodeClause_clauseBytes {n : ℕ} (C : List (SAT.Literal (Fin n))) :
    decodeClause n (clauseBytes C) = some C :=
  decodeRecords_encode literalBytes (decodeLiteral n) decodeLiteral_literalBytes C

def decodeLeaf (n : ℕ) : List Bool → Option (Leaf n) :=
  decodeRecords (decodeClause n)

theorem encodeRawFormula_eq {n : ℕ} (G : Leaf n) :
    ExecQuantitativeSparsify.encodeRawFormula G = Encoding.encodeList clauseBytes G := by
  simp only [ExecQuantitativeSparsify.encodeRawFormula,
    ExecSparsifyEncoding.encodeList_map]
  rfl

@[simp] theorem decodeLeaf_encodeRawFormula {n : ℕ} (G : Leaf n) :
    decodeLeaf n (ExecQuantitativeSparsify.encodeRawFormula G) = some G := by
  rw [encodeRawFormula_eq]
  exact decodeRecords_encode clauseBytes (decodeClause n) decodeClause_clauseBytes G

theorem encodeRawFormula_injective (n : ℕ) :
    Function.Injective (ExecQuantitativeSparsify.encodeRawFormula (n := n)) := by
  intro G H h
  have hd := congrArg (decodeLeaf n) h
  simpa only [decodeLeaf_encodeRawFormula, Option.some.injEq] using hd

/-- A reference answer on bytes. It is never used as a machine instruction. -/
def test (n : ℕ) (bits : List Bool) : Bool :=
  match decodeLeaf n bits with
  | some G => SAT.bruteForce (ExecCNF.formulaSet G)
  | none => false

@[simp] theorem test_encodeRawFormula {n : ℕ} (G : Leaf n) :
    test n (ExecQuantitativeSparsify.encodeRawFormula G) =
      SAT.bruteForce (ExecCNF.formulaSet G) := by
  simp only [test, decodeLeaf_encodeRawFormula]

theorem test_encodeRawFormula_iff {n : ℕ} (G : Leaf n) :
    test n (ExecQuantitativeSparsify.encodeRawFormula G) = true ↔
      SAT.Satisfiable (ExecCNF.formulaSet G) := by
  rw [test_encodeRawFormula, SAT.bruteForce_eq_true_iff]

/-- The logical property of leaves may be the actual sparsifier invariant.
The encoding witnesses preserve the complete observed list order. -/
def validPayload (n : ℕ) (valid : Leaf n → Prop) (bits : List Bool) : Prop :=
  ∃ G : Leaf n, valid G ∧ bits = ExecQuantitativeSparsify.encodeRawFormula G

structure Sparse {n : ℕ} (k B : ℕ) (G : Leaf n) : Prop where
  clause_sets_nodup : (G.map ExecCNF.clauseSet).Nodup
  width : SAT.WidthAtMost k (ExecCNF.formulaSet G)
  occurrences : SAT.OccurrenceAtMost B (ExecCNF.formulaSet G)

theorem validPayload_encoded {n : ℕ} {valid : Leaf n → Prop} {bits : List Bool}
    (h : validPayload n valid bits) :
    ∃ records : List (List Bool), bits = Encoding.encodeList id records := by
  rcases h with ⟨G, _, rfl⟩
  refine ⟨G.map clauseBytes, ?_⟩
  rw [ExecSparsifyEncoding.encodeList_map, encodeRawFormula_eq]
  rfl

theorem empty_answer {n : ℕ} {valid : Leaf n → Prop} {bits : List Bool}
    (h : validPayload n valid bits) (he : SubexpEmptyClauseGuard.HasEmpty bits) :
    test n bits = false := by
  rcases h with ⟨G, _, rfl⟩
  have hn := SubexpEmptyClauseGuard.hasEmpty_raw_unsatisfiable G he
  have ht := test_encodeRawFormula_iff G
  cases hb : test n (ExecQuantitativeSparsify.encodeRawFormula G) <;> simp_all

theorem nonempty_clauses {n : ℕ} (G : Leaf n)
    (h : ¬ SubexpEmptyClauseGuard.HasEmpty (ExecQuantitativeSparsify.encodeRawFormula G)) :
    ∀ C ∈ ExecCNF.formulaSet G, C.Nonempty := by
  apply SubexpLeafData.clauses_nonempty G
  exact fun he => h ((SubexpEmptyClauseGuard.hasEmpty_raw_iff G).mpr he)

section Packed

variable {n ell p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  (G : Leaf n) (hell : 0 < ell) (hcap : 2 ^ ell ≤ p)

local notation "S" => SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)
local notation "D" => Fintype.card (Fin (ChunkPartition.count n ell))
local notation "B" => SubexpLiftRing.baseWidth p (D + 1)
local notation "coeffs" => QuarticSearch.liftedCoefficients p (D + 1)

theorem packed_satisfiable :
    (∃ x, Factor.Satisfies S x) ↔ SAT.Satisfiable (ExecCNF.formulaSet G) := by
  rw [← Factor.count_pos_iff, SubexpLEFactorSystem.packed_count, SAT.count_pos_iff]

include hell in
theorem chunks_pos (hn : 0 < n) : 0 < D := by
  simpa only [Fintype.card_fin] using (ChunkPartition.count_pos_iff hell).mpr hn

variable {c : Parameters p k Δ r tau}

theorem answer_iff (L : Layout (E := SubexpActualRing.E p) (S).toPattern c)
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (output : SubexpFlatCount.Code B) (hn : 0 < n)
    (computed : SubexpHornerMachine.decode p (D + 1) coeffs output =
      SubexpCRTAtZero.selectedValue S L) :
    SubexpDecodeProgram.answer M.bits output.c0.val = true ↔
      SAT.Satisfiable (ExecCNF.formulaSet G) :=
  (SubexpH0CountDecision.answer_iff S L M output (chunks_pos hell hn) computed).trans
    (packed_satisfiable G hell hcap)

/-- This invokes the real finalizer on the single H(0) quartet. The caller
must still provide its actual reconstruction denotation and input state. -/
theorem finalize_execution (L : Layout (E := SubexpActualRing.E p) (S).toPattern c)
    {er es : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (output : SubexpFlatCount.Code B) (hn : 0 < n)
    (computed : SubexpHornerMachine.decode p (D + 1) coeffs output =
      SubexpCRTAtZero.selectedValue S L)
    (a : MainState er es) (regs : Fin 8 → Bool) (width : List Bool)
    (hwidth : width.length = B)
    (ready : (SubexpMainDecode.procedure er es).project a =
      SubexpFlatCount.start regs M.bits width (SubexpFlatCount.flatPolynomial [output])) :
    ∃ (steps : ℕ) (rf : Fin 8 → Bool),
      steps ≤ 3 * SubexpH0CountDecision.budget B +
        2 * WorkspaceCleanupProgram.Main.selectedBits count hcount a +
        3 * count + workRegs er + 4 ∧
      Eval (SubexpMainReady.procedure er es count hcount).invoke steps a
        (SubexpMainReady.result count hcount a rf M.bits width output.c0.val) ∧
      SubexpMainReady.StorageReady count
        (SubexpMainReady.result count hcount a rf M.bits width output.c0.val) ∧
      (((SubexpMainReady.result count hcount a rf M.bits width output.c0.val).stacks
        (persistent es 10)).head? = some true ↔ SAT.Satisfiable (ExecCNF.formulaSet G)) ∧
      (∀ j : Fin 32, j ≠ 10 →
        (SubexpMainReady.result count hcount a rf M.bits width output.c0.val).stacks
          (persistent es j) = a.stacks (persistent es j)) := by
  obtain ⟨steps, rf, hb, he, hr, ha, hf⟩ := SubexpH0Finalize.execution S L
    count hcount M output (chunks_pos hell hn) computed a regs width hwidth ready
  exact ⟨steps, rf, hb, he, hr, ha.trans (packed_satisfiable G hell hcap), hf⟩

end Packed

end SubexponentialSAT.SubexpLeafSemantics

end OAI.Algorithms
