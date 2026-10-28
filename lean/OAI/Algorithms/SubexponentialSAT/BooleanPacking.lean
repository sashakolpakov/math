import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Boolean chunks and valid finite-field labels

This file implements the encoding in Section 3 of the candidate exposition.
The encoding is an actual recursively defined equivalence, not just an equality
of cardinalities. Primality is unnecessary for this combinatorial part.
-/

namespace SubexponentialSAT.BooleanPacking

open scoped BigOperators

/-- The manuscript's logarithmic chunk-size choice supplies enough labels. -/
theorem capacity_of_le_log {b p : ℕ} (hp : p ≠ 0) (hb : b ≤ Nat.log 2 p) :
    2 ^ b ≤ p :=
  Nat.pow_le_of_le_log hp hb

/-- The equivalent `Nat.log2` formulation of the chunk-size bound. -/
theorem capacity_of_le_log2 {b p : ℕ} (hp : p ≠ 0) (hb : b ≤ Nat.log2 p) :
    2 ^ b ≤ p :=
  capacity_of_le_log hp (by simpa only [Nat.log2_eq_log_two] using hb)

/-- A chunk of `b` Boolean coordinates. Empty chunks are allowed by the API. -/
abbrev Chunk (b : ℕ) := Fin b → Bool

/-- Splitting a nonempty chunk into its first bit and remaining bits. -/
def splitChunk (b : ℕ) : Chunk (b + 1) ≃ Bool × Chunk b where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv x := by
    rcases x with ⟨head, tail⟩
    rfl

/-- A computable encoding of a Boolean chunk by exactly `2^b` labels. -/
def chunkEquiv : (b : ℕ) → Chunk b ≃ Fin (2 ^ b)
  | 0 => by simpa only [pow_zero] using Equiv.ofUnique (Chunk 0) (Fin 1)
  | b + 1 =>
      (splitChunk b).trans <|
        (Equiv.prodCongr finTwoEquiv.symm (chunkEquiv b)).trans <|
          finProdFinEquiv.trans (finCongr (by simp [pow_succ, Nat.mul_comm]))

/-- The allowed labels for a `b`-bit chunk inside `Fin p`. -/
def ValidLabel (b p : ℕ) := {x : Fin p // x.val < 2 ^ b}

instance (b p : ℕ) : Fintype (ValidLabel b p) :=
  inferInstanceAs (Fintype {x : Fin p // x.val < 2 ^ b})

/-- Including the initial segment of length `2^b` into a larger label space. -/
def finValidLabelEquiv {b p : ℕ} (h : 2 ^ b ≤ p) :
    Fin (2 ^ b) ≃ ValidLabel b p where
  toFun x := ⟨⟨x.val, lt_of_lt_of_le x.isLt h⟩, x.isLt⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Encoding and decoding a chunk using precisely the valid labels. -/
def validLabelEquiv {b p : ℕ} (h : 2 ^ b ≤ p) : Chunk b ≃ ValidLabel b p :=
  (chunkEquiv b).trans (finValidLabelEquiv h)

/-- The chunk encoding into the complete label space, including invalid labels. -/
def chunkEmbedding {b p : ℕ} (h : 2 ^ b ≤ p) : Chunk b ↪ Fin p where
  toFun x := (validLabelEquiv h x).val
  inj' _ _ heq := (validLabelEquiv h).injective (Subtype.ext heq)

/-- Decoding is defined on valid labels. -/
def decode {b p : ℕ} (h : 2 ^ b ≤ p) (x : ValidLabel b p) : Chunk b :=
  (validLabelEquiv h).symm x

@[simp] theorem decode_encode {b p : ℕ} (h : 2 ^ b ≤ p) (x : Chunk b) :
    decode h (validLabelEquiv h x) = x :=
  (validLabelEquiv h).symm_apply_apply x

@[simp] theorem encode_decode {b p : ℕ} (h : 2 ^ b ≤ p) (x : ValidLabel b p) :
    validLabelEquiv h (decode h x) = x :=
  (validLabelEquiv h).apply_symm_apply x

theorem chunkEmbedding_valid {b p : ℕ} (h : 2 ^ b ≤ p) (x : Chunk b) :
    (chunkEmbedding h x).val < 2 ^ b :=
  (validLabelEquiv h x).property

theorem mem_range_chunkEmbedding {b p : ℕ} (h : 2 ^ b ≤ p) (a : Fin p) :
    a ∈ Set.range (chunkEmbedding h) ↔ a.val < 2 ^ b := by
  constructor
  · rintro ⟨x, rfl⟩
    exact chunkEmbedding_valid h x
  · intro ha
    refine ⟨decode h ⟨a, ha⟩, ?_⟩
    exact congrArg Subtype.val (encode_decode h ⟨a, ha⟩)

theorem card_chunk (b : ℕ) : Fintype.card (Chunk b) = 2 ^ b := by
  calc
    _ = Fintype.card (Fin (2 ^ b)) := Fintype.card_congr (chunkEquiv b)
    _ = _ := Fintype.card_fin _

theorem card_validLabel {b p : ℕ} (h : 2 ^ b ≤ p) :
    Fintype.card (ValidLabel b p) = 2 ^ b := by
  calc
    _ = Fintype.card (Fin (2 ^ b)) := Fintype.card_congr (finValidLabelEquiv h).symm
    _ = _ := Fintype.card_fin _

/-- All chunk-label assignments accepted by the unary validity tests. -/
def PackedAssignment {J : Type*} (b : J → ℕ) (p : ℕ) :=
  {x : J → Fin p // ∀ j, (x j).val < 2 ^ b j}

instance {J : Type*} [Fintype J] [DecidableEq J] (b : J → ℕ) (p : ℕ) :
    Fintype (PackedAssignment b p) :=
  inferInstanceAs (Fintype {x : J → Fin p // ∀ j, (x j).val < 2 ^ b j})

/-- Coordinatewise chunk encoding, with validity built into the codomain. -/
def packingEquiv {J : Type*} (b : J → ℕ) {p : ℕ} (h : ∀ j, 2 ^ b j ≤ p) :
    (∀ j, Chunk (b j)) ≃ PackedAssignment b p :=
  (Equiv.piCongrRight fun j => validLabelEquiv (h j)).trans
    Equiv.subtypePiEquivPi.symm

@[simp] theorem packingEquiv_apply {J : Type*} (b : J → ℕ) {p : ℕ}
    (h : ∀ j, 2 ^ b j ≤ p) (x : ∀ j, Chunk (b j)) (j : J) :
    (packingEquiv b h x).val j = chunkEmbedding (h j) (x j) := rfl

@[simp] theorem packingEquiv_symm_apply {J : Type*} (b : J → ℕ) {p : ℕ}
    (h : ∀ j, 2 ^ b j ≤ p) (x : PackedAssignment b p) (j : J) :
    (packingEquiv b h).symm x j = decode (h j) ⟨x.val j, x.property j⟩ := rfl

/-- An index for each original bit, recording both its chunk and position. -/
abbrev BitIndex {J : Type*} (b : J → ℕ) := Σ j, Fin (b j)

/-- Regrouping Boolean coordinates requires no assignments to be discarded. -/
def regroupEquiv {J : Type*} (b : J → ℕ) :
    (BitIndex b → Bool) ≃ (∀ j, Chunk (b j)) :=
  Equiv.piCurry fun _ _ => Bool

/-- Encoding a flat Boolean assignment into accepted chunk labels. -/
def flatPackingEquiv {J : Type*} (b : J → ℕ) {p : ℕ} (h : ∀ j, 2 ^ b j ≤ p) :
    (BitIndex b → Bool) ≃ PackedAssignment b p :=
  (regroupEquiv b).trans (packingEquiv b h)

/-- A concrete partition of the original variable indices transports packing
to the original assignment type. -/
def assignmentPackingEquiv {V J : Type*} (b : J → ℕ) (indices : V ≃ BitIndex b)
    {p : ℕ} (h : ∀ j, 2 ^ b j ≤ p) :
    (V → Bool) ≃ PackedAssignment b p :=
  (Equiv.arrowCongr indices (Equiv.refl Bool)).trans (flatPackingEquiv b h)

/-- The satisfying assignments for any predicate correspond under encoding. -/
def satisfyingEquiv {J : Type*} (b : J → ℕ) {p : ℕ} (h : ∀ j, 2 ^ b j ≤ p)
    (P : (∀ j, Chunk (b j)) → Prop) :
    {x // P x} ≃ {y : PackedAssignment b p // P ((packingEquiv b h).symm y)} :=
  (packingEquiv b h).subtypeEquiv (by intro x; simp)

/-- Exact finite model-count preservation, not just satisfiability preservation. -/
theorem count_preserved {J : Type*} [Fintype J] [DecidableEq J] (b : J → ℕ)
    {p : ℕ} (h : ∀ j, 2 ^ b j ≤ p) (P : (∀ j, Chunk (b j)) → Prop)
    [DecidablePred P] :
    Fintype.card {x // P x} =
      Fintype.card {y : PackedAssignment b p // P ((packingEquiv b h).symm y)} :=
  Fintype.card_congr (satisfyingEquiv b h P)

/-- The exact model-count theorem also applies to any partition of original
Boolean variable indices into chunks. -/
theorem assignment_count_preserved {V J : Type*} [Fintype V] [DecidableEq V]
    [Fintype J] [DecidableEq J] (b : J → ℕ) (indices : V ≃ BitIndex b)
    {p : ℕ} (h : ∀ j, 2 ^ b j ≤ p) (P : (V → Bool) → Prop) [DecidablePred P] :
    Fintype.card {x // P x} =
      Fintype.card {y : PackedAssignment b p //
        P ((assignmentPackingEquiv b indices h).symm y)} := by
  apply Fintype.card_congr
  exact (assignmentPackingEquiv b indices h).subtypeEquiv (by intro x; simp)

theorem card_packedAssignment {J : Type*} [Fintype J] [DecidableEq J]
    (b : J → ℕ) {p : ℕ} (h : ∀ j, 2 ^ b j ≤ p) :
    Fintype.card (PackedAssignment b p) = 2 ^ (∑ j, b j) := by
  calc
    Fintype.card (PackedAssignment b p) = Fintype.card (∀ j, Chunk (b j)) :=
      Fintype.card_congr (packingEquiv b h).symm
    _ = ∏ j, Fintype.card (Chunk (b j)) := Fintype.card_pi
    _ = ∏ j, 2 ^ b j := by simp only [card_chunk]
    _ = 2 ^ (∑ j, b j) := Finset.prod_pow_eq_pow_sum _ _ _

/-- The finite label equivalence preserves the usual representatives in `ZMod`. -/
@[simp] theorem finEquiv_val {p : ℕ} [NeZero p] (x : Fin p) :
    (ZMod.finEquiv p x).val = x.val := by
  cases p with
  | zero => exact (NeZero.ne (0 : ℕ) rfl).elim
  | succ p => rfl

/-- Valid representatives inside `ZMod p`. For prime `p`, these are field labels. -/
def ValidZModLabel (b p : ℕ) := {x : ZMod p // x.val < 2 ^ b}

/-- The same explicit encoding in the residue ring, hence in the prime field. -/
def validZModEquiv {b p : ℕ} [NeZero p] (h : 2 ^ b ≤ p) :
    Chunk b ≃ ValidZModLabel b p :=
  (validLabelEquiv h).trans <|
    (ZMod.finEquiv p).toEquiv.subtypeEquiv (by intro x; simp)

/-- Encoding a Boolean chunk as a residue-ring element. -/
def chunkZModEmbedding {b p : ℕ} [NeZero p] (h : 2 ^ b ≤ p) :
    Chunk b ↪ ZMod p where
  toFun x := (validZModEquiv h x).val
  inj' _ _ heq := (validZModEquiv h).injective (Subtype.ext heq)

theorem mem_range_chunkZModEmbedding {b p : ℕ} [NeZero p] (h : 2 ^ b ≤ p)
    (a : ZMod p) : a ∈ Set.range (chunkZModEmbedding h) ↔ a.val < 2 ^ b := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (validZModEquiv h x).property
  · intro ha
    refine ⟨(validZModEquiv h).symm ⟨a, ha⟩, ?_⟩
    exact congrArg Subtype.val ((validZModEquiv h).apply_symm_apply ⟨a, ha⟩)

end SubexponentialSAT.BooleanPacking

end OAI.Algorithms
