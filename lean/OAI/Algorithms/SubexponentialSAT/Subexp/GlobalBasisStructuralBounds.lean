import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMatrixRows
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisComplementBounds

namespace OAI.Algorithms

/-!
# Structural polynomial bounds for physical global-basis assembly

The size parameter is the sum of serialized input lengths and unary counts.
Metadata fields are bounded using successful lookups, and local-table fields
using their actual framed records in the batch. No execution or cost witness
is assumed by any bound below.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisStructuralBounds

open GlobalBasisInput (Context Location)
open GlobalBasisProgram

variable {p r Q Δ : ℕ} [Fact p.Prime]

def inputSize (C : Context p r Q Δ) (xs : List GlobalBasisColumns.Descriptor)
    (rowCount : ℕ) : ℕ :=
  (SelectorProgram.rawRecords C.metadata).length + C.batch.length +
    (ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ)).length +
    r + C.position.val + rowCount + GlobalBasisEntry.frameWidth p +
    GlobalBasisRows.encodedSize xs + 1

def volume (C : Context p r Q Δ) (locs : List (Location r Q Δ))
    (xs : List GlobalBasisColumns.Descriptor) : ℕ := inputSize C xs locs.length

theorem inputSize_pos (C : Context p r Q Δ) (xs : List GlobalBasisColumns.Descriptor)
    (rowCount : ℕ) : 0 < inputSize C xs rowCount := by unfold inputSize; omega

/-- Dimension, split, and actual table bytes all occur in one retained batch record. -/
theorem local_fields_le_batch (C : Context p r Q Δ) (g : Fin r) :
    (C.tables g).dimension + (C.tables g).split + (C.tables g).bits.length ≤ C.batch.length := by
  have hm : (C.tables g).data ∈ C.data := by
    apply List.mem_ofFn.mpr
    exact ⟨g, rfl⟩
  have hf := GlobalBasisComplementColumns.payload_fields_le (C.tables g).data
  have hb := GlobalBasisComplementColumns.member_payload_le hm
  exact hf.trans hb

omit [Fact p.Prime] in
/-- Successful lookup bounds the encoded block and type by the metadata bytes. -/
theorem covered_fields_le_metadata (C : Context p r Q Δ) (index block : ℕ)
    (u : MulticolorTypes.UniversalType r Q Δ) (hm : C.matches index (.covered block u)) :
    block + (CollisionProgram.encodeType u).length ≤
      (SelectorProgram.rawRecords C.metadata).length := by
  have h := GlobalBasisMetadata.payload_length_le C.metadata (List.replicate index true)
    (Location.metadata (.covered block u)).encode hm
  simp only [Location.metadata, GlobalBasisMetadata.Metadata.encode,
    List.length_cons, List.length_append, Encoding.length_frame, List.length_replicate] at h
  omega

omit [Fact p.Prime] in
theorem leftover_rank_le_metadata (C : Context p r Q Δ) (index rank : ℕ)
    (hm : C.matches index (.leftover rank)) :
    rank ≤ (SelectorProgram.rawRecords C.metadata).length := by
  have h := GlobalBasisMetadata.payload_length_le C.metadata (List.replicate index true)
    (Location.metadata (.leftover rank : Location r Q Δ)).encode hm
  simp only [Location.metadata, GlobalBasisMetadata.Metadata.encode,
    List.length_cons, Encoding.length_frame, List.length_replicate] at h
  omega

omit [Fact p.Prime] in
theorem coordinate_le_dimension (C : Context p r Q Δ)
    (u : MulticolorTypes.UniversalType r Q Δ) :
    GlobalBasisCoveredRow.coordinate u C.position ≤ (C.tables (u.head C.position)).dimension := by
  have h := (GlobalBasisCoveredRow.coordinate_lt u C.position).le
  rw [C.dimensions]
  exact h

theorem rowDataSize_le (C : Context p r Q Δ) (index : ℕ) (loc : Location r Q Δ)
    (hm : C.matches index loc) :
    rowDataSize (C.row loc) ≤ 2 * C.batch.length +
      (SelectorProgram.rawRecords C.metadata).length + r := by
  cases loc with
  | leftover rank =>
    have h := leftover_rank_le_metadata C index rank hm
    have h' : rank ≤ 2 * C.batch.length + (SelectorProgram.rawRecords C.metadata).length + r := by
      omega
    simpa [rowDataSize, Context.row, GlobalBasisRowPrepare.leftoverRow,
      BasisTransposeProgram.rows] using h'
  | covered block u =>
    have hf := local_fields_le_batch C (u.head C.position)
    have hm := covered_fields_le_metadata C index block u hm
    have hc := coordinate_le_dimension C u
    have hg := (u.head C.position).isLt.le
    change (C.tables (u.head C.position)).bits.length +
      (C.tables (u.head C.position)).dimension + GlobalBasisCoveredRow.coordinate u C.position +
      block + (u.head C.position).val + 0 ≤ _
    omega

theorem baseSize_le (C : Context p r Q Δ) (index : ℕ) (loc : Location r Q Δ)
    (hm : C.matches index loc) :
    GlobalBasisRows.baseSize (C.row loc) ≤ 2 * C.batch.length +
      (SelectorProgram.rawRecords C.metadata).length + r + GlobalBasisEntry.frameWidth p + 1 := by
  cases loc with
  | leftover rank =>
    have h := leftover_rank_le_metadata C index rank hm
    simp only [GlobalBasisRows.baseSize, Context.row, GlobalBasisRowPrepare.leftoverRow]
    omega
  | covered block u =>
    have hf := local_fields_le_batch C (u.head C.position)
    have hm := covered_fields_le_metadata C index block u hm
    have hc := coordinate_le_dimension C u
    have hg := (u.head C.position).isLt.le
    change (C.tables (u.head C.position)).dimension + GlobalBasisCoveredRow.coordinate u C.position +
      block + (u.head C.position).val + 0 + GlobalBasisEntry.frameWidth p + 1 ≤ _
    omega

/-- The preparation cap follows from input bytes, including possibly padded
or redundant metadata records, rather than from an assumed runtime certificate. -/
theorem setupBudget_le (C : Context p r Q Δ) (xs : List GlobalBasisColumns.Descriptor)
    (rowCount index : ℕ) (loc : Location r Q Δ)
    (hm : C.matches index loc) (hi : index ≤ rowCount) :
    C.setupBudget index loc ≤ 1000 * (inputSize C xs rowCount + 1)^3 := by
  let V := inputSize C xs rowCount
  let A := V + 1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have h13 : A ≤ A^3 := by
    simpa using Nat.pow_le_pow_right hA (show 1 ≤ 3 by decide)
  have h23 : A^2 ≤ A^3 := Nat.pow_le_pow_right hA (by decide)
  have hv : GlobalBasisMetadata.volume C.metadata (List.replicate index true) ≤ A := by
    simp only [GlobalBasisMetadata.volume, List.length_replicate]
    dsimp [A, V, inputSize]
    omega
  have hv2 := Nat.pow_le_pow_left hv 2
  cases loc with
  | leftover rank =>
    change 400 * (GlobalBasisMetadata.volume C.metadata (List.replicate index true))^2 + 5 ≤
      1000 * A^3
    nlinarith only [hv2, hA, h13, h23]
  | covered block u =>
    have hfields := covered_fields_le_metadata C index block u hm
    have hlocal := local_fields_le_batch C (u.head C.position)
    have hr : r ≤ V := by dsimp [V, inputSize]; omega
    have ht : C.position.val ≤ V := by dsimp [V, inputSize]; omega
    have hq : (CollisionProgram.encodeType u).length ≤ V := by dsimp [V, inputSize]; omega
    have hu : (ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ)).length ≤ V := by
      dsimp [V, inputSize]; omega
    have hb : C.batch.length ≤ V := by dsimp [V, inputSize]; omega
    have hN : (C.tables (u.head C.position)).dimension ≤ V := by dsimp [V, inputSize]; omega
    have hs : (C.tables (u.head C.position)).split ≤ V := by dsimp [V, inputSize]; omega
    have hp := GlobalBasisCoveredRow.budget_le u C.position
      (C.tables (u.head C.position)).dimension (C.tables (u.head C.position)).split C.batch V
      hr ht hq hu hb hN hs
    change GlobalBasisCoveredRow.budget u C.position
      (C.tables (u.head C.position)).dimension (C.tables (u.head C.position)).split C.batch + 1 ≤
      500 * A^3 at hp
    change (400 * (GlobalBasisMetadata.volume C.metadata (List.replicate index true))^2 + 1 +
      GlobalBasisCoveredRow.budget u C.position (C.tables (u.head C.position)).dimension
        (C.tables (u.head C.position)).split C.batch +
      2 * (CollisionProgram.encodeType u).length + 3) + 1 ≤ 1000 * A^3
    have hqA : (CollisionProgram.encodeType u).length ≤ A := hq.trans (by dsimp [A]; omega)
    nlinarith only [hv2, hp, hqA, hA, h13, h23]

theorem rowBudget_le (C : Context p r Q Δ) (xs : List GlobalBasisColumns.Descriptor)
    (rowCount index : ℕ) (loc : Location r Q Δ)
    (hm : C.matches index loc) (hi : index ≤ rowCount) :
    rowBudget C index loc xs ≤ 40000 * (inputSize C xs rowCount + 1)^4 := by
  let V := inputSize C xs rowCount
  let A := V + 1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have h14 : A ≤ A^4 := by simpa using Nat.pow_le_pow_right hA (show 1 ≤ 4 by decide)
  have h34 : A^3 ≤ A^4 := Nat.pow_le_pow_right hA (by decide)
  have hs := setupBudget_le C xs rowCount index loc hm hi
  have hb := baseSize_le C index loc hm
  have hd := rowDataSize_le C index loc hm
  have hbase : GlobalBasisRows.baseSize (C.row loc) + GlobalBasisRows.encodedSize xs + 1 ≤ 2 * A := by
    dsimp [A, V, inputSize]
    omega
  have hdata : rowDataSize (C.row loc) ≤ 2 * A := by dsimp [A, V, inputSize]; omega
  have hdesc : GlobalBasisRows.encodedSize xs ≤ A := by dsimp [A, V, inputSize]; omega
  have hpow := Nat.pow_le_pow_left hbase 4
  change C.setupBudget index loc ≤ 1000 * A^3 at hs
  change rowBudget C index loc xs ≤ 40000 * A^4
  unfold rowBudget
  nlinarith only [hs, hpow, hdata, hdesc, hA, h14, h34]

theorem rowsBudget_le_count (C : Context p r Q Δ) (xs : List GlobalBasisColumns.Descriptor)
    (rowCount : ℕ) (locs : List (Location r Q Δ)) :
    ∀ index, C.locations index locs → index + locs.length ≤ rowCount →
      rowsBudget C xs index locs ≤
        locs.length * (40000 * (inputSize C xs rowCount + 1)^4 + 2) + 2 := by
  induction locs with
  | nil => intro index hm hi; simp [rowsBudget]
  | cons loc locs ih =>
    intro index hm hi
    have hindex : index ≤ rowCount := by simp only [List.length_cons] at hi; omega
    have htail : index + 1 + locs.length ≤ rowCount := by
      simp only [List.length_cons] at hi
      omega
    have hb := rowBudget_le C xs rowCount index loc hm.1 hindex
    have ht := ih (index+1) hm.2 htail
    simp only [rowsBudget, List.length_cons]
    nlinarith only [hb, ht]

theorem rowsBudget_le (C : Context p r Q Δ) (xs : List GlobalBasisColumns.Descriptor)
    (rowCount index : ℕ) (locs : List (Location r Q Δ))
    (hm : C.locations index locs) (hi : index + locs.length ≤ rowCount) :
    rowsBudget C xs index locs ≤ 50000 * (inputSize C xs rowCount + 1)^5 := by
  let A := inputSize C xs rowCount + 1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hn : locs.length ≤ A := by dsimp [A, inputSize]; omega
  have h15 : A ≤ A^5 := by simpa using Nat.pow_le_pow_right hA (show 1 ≤ 5 by decide)
  have hb := rowsBudget_le_count C xs rowCount locs index hm hi
  have hmul := Nat.mul_le_mul_right (40000 * A^4 + 2) hn
  change rowsBudget C xs index locs ≤ locs.length * (40000 * A^4 + 2) + 2 at hb
  change rowsBudget C xs index locs ≤ 50000 * A^5
  nlinarith only [hb, hmul, hA, h15]

omit [Fact p.Prime] in
theorem matrixBits_length (C : Context p r Q Δ) (locs : List (Location r Q Δ))
    (xs : List GlobalBasisColumns.Descriptor) :
    (matrixBits C locs xs).length = locs.length * xs.length * GlobalBasisEntry.frameWidth p := by
  induction locs with
  | nil => simp [matrixBits]
  | cons loc locs ih =>
    simp only [matrixBits, List.flatMap_cons, List.length_append, GlobalBasisRows.rowBits_length,
      List.length_cons] at ih ⊢
    rw [ih]
    ring

theorem matrixBudget_le (C : Context p r Q Δ) (locs : List (Location r Q Δ))
    (xs : List GlobalBasisColumns.Descriptor) (hm : C.locations 0 locs) :
    matrixBudget C xs locs ≤ 1000000 * (volume C locs xs + 1)^6 := by
  let A := volume C locs xs + 1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hn : locs.length ≤ A := by dsimp [A, volume, inputSize]; omega
  have hx : xs.length ≤ A := (GlobalBasisRows.length_le_encodedSize xs).trans (by
    dsimp [A, volume, inputSize]; omega)
  have hf : GlobalBasisEntry.frameWidth p ≤ A := by dsimp [A, volume, inputSize]; omega
  have hdesc : GlobalBasisRows.encodedSize xs ≤ A := by dsimp [A, volume, inputSize]; omega
  have hout : (matrixBits C locs xs).length ≤ A^3 := by
    rw [matrixBits_length]
    calc
      _ ≤ A * A * A := Nat.mul_le_mul (Nat.mul_le_mul hn hx) hf
      _ = _ := by ring
  have hrows := rowsBudget_le C xs locs.length 0 locs hm (by omega)
  change rowsBudget C xs 0 locs ≤ 50000 * A^5 at hrows
  have hcount := countBudget_le (GlobalBasisRows.records xs)
  change countBudget (GlobalBasisRows.records xs) ≤ 13 * GlobalBasisRows.encodedSize xs + 4 at hcount
  have h16 : A ≤ A^6 := by simpa using Nat.pow_le_pow_right hA (show 1 ≤ 6 by decide)
  have h36 : A^3 ≤ A^6 := Nat.pow_le_pow_right hA (by decide)
  have h56 : A^5 ≤ A^6 := Nat.pow_le_pow_right hA (by decide)
  change matrixBudget C xs locs ≤ 1000000 * A^6
  unfold matrixBudget
  nlinarith only [hrows, hcount, hout, hn, hdesc, hA, h16, h36, h56]

end SubexponentialSAT.Subexp.GlobalBasisStructuralBounds

end OAI.Algorithms
