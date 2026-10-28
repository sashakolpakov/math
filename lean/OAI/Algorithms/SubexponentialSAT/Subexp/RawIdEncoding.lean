import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Encoding
import OAI.Algorithms.SubexponentialSAT.ExecCNF
import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

namespace OAI.Algorithms

/-!
# External CNF syntax with explicit binary variable identifiers

A literal payload is `frame identifier ++ [positive]`. A clause is an
encoded list of these payloads, and a formula is an encoded list of clauses.
There is no maximum-ID header. Identifiers are compared as bit words; the
numeric adapter uses canonical little-endian `Nat.bits` (zero is empty).
-/

namespace SubexponentialSAT.Subexp.RawIdEncoding

abbrev Word := List Bool
abbrev Literal := SAT.Literal Word
abbrev Clause := List Literal
abbrev Formula := List Clause

def literalBytes (l : Literal) : Word := Encoding.frame l.variable ++ [l.positive]
def clauseBytes (C : Clause) : Word := Encoding.encodeList literalBytes C
def encode (F : Formula) : Word := Encoding.encodeList clauseBytes F

def ids (F : Formula) : List Word := F.flatten.map SAT.Literal.variable

/-- The collector prepends records, then the existing stable deduplicator
retains the last occurrence in that physical order. -/
def dictionary (F : Formula) : List Word := ExecCNF.dedupLiterals ((ids F).reverse)

def dimension (F : Formula) : ℕ := (dictionary F).length

def semantics (F : Formula) : SAT.CNF Word := ExecCNF.formulaSet F

def numericLiteral (l : SAT.Literal ℕ) : Literal := ⟨Nat.bits l.variable, l.positive⟩
def numericFormula (F : List (List (SAT.Literal ℕ))) : Formula :=
  F.map (List.map numericLiteral)

@[simp] theorem literalBytes_length (l : Literal) :
    (literalBytes l).length = 2 * l.variable.length + 2 := by
  simp [literalBytes]

theorem literalBytes_injective : Function.Injective literalBytes := by
  intro a b h
  obtain ⟨hv, hp⟩ := Encoding.frame_append_injective h
  have hp' : a.positive = b.positive := by simpa using hp
  cases a; cases b; cases hv; cases hp'; rfl

theorem clauseBytes_injective : Function.Injective clauseBytes :=
  Encoding.encodeList_injective literalBytes_injective

theorem encode_injective : Function.Injective encode :=
  Encoding.encodeList_injective clauseBytes_injective

@[simp] theorem dictionary_nodup (F : Formula) : (dictionary F).Nodup :=
  ExecCNF.dedupLiterals_nodup _

@[simp] theorem mem_dictionary (F : Formula) (id : Word) :
    id ∈ dictionary F ↔ id ∈ ids F := by
  simp [dictionary]

theorem literal_id_mem (F : Formula) (C : Clause) (hC : C ∈ F)
    (l : Literal) (hl : l ∈ C) : l.variable ∈ dictionary F := by
  rw [mem_dictionary]
  exact List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨C, hC, hl⟩, rfl⟩

theorem dimension_le_occurrences (F : Formula) : dimension F ≤ F.flatten.length := by
  simpa only [dimension, dictionary, ids, List.length_reverse, List.length_map] using
    ExecCNF.dedupLiterals_length_le (ids F).reverse

theorem clause_length_le_bytes (C : Clause) : C.length ≤ (clauseBytes C).length :=
  (Nat.le_succ C.length).trans (Encoding.length_encodeList_lower literalBytes C)

theorem occurrences_le_bytes (F : Formula) : F.flatten.length ≤ (encode F).length := by
  induction F with
  | nil => simp [encode]
  | cons C F ih =>
      have hc := clause_length_le_bytes C
      simp only [List.flatten_cons, List.length_append, encode,
        Encoding.length_encodeList_cons] at *
      omega

theorem dimension_le_bytes (F : Formula) : dimension F ≤ (encode F).length :=
  (dimension_le_occurrences F).trans (occurrences_le_bytes F)

theorem formula_length_le_bytes (F : Formula) : F.length ≤ (encode F).length :=
  (Nat.le_succ F.length).trans (Encoding.length_encodeList_lower clauseBytes F)

theorem clause_length_le_input (F : Formula) (C : Clause) (hC : C ∈ F) :
    C.length ≤ (encode F).length := by
  have hc : C.length ≤ F.flatten.length := by
    induction F with
    | nil => simp at hC
    | cons D F ih =>
        simp only [List.mem_cons] at hC
        rcases hC with rfl | hC
        · simp
        · exact (ih hC).trans (by simp)
  exact hc.trans (occurrences_le_bytes F)

@[simp] theorem value_numericId (n : ℕ) : BinaryArithmetic.toNat (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn, BinaryArithmetic.toNat_cons, ih]
      cases b <;> simp [Nat.bit, BinaryArithmetic.bitVal, Nat.add_comm]

theorem numericId_injective : Function.Injective Nat.bits := by
  intro a b h
  simpa only [value_numericId] using congrArg BinaryArithmetic.toNat h

end SubexponentialSAT.Subexp.RawIdEncoding

end OAI.Algorithms
