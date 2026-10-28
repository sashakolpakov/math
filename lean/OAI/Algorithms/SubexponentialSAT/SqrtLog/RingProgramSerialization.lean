import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramWords

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgram

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

/-- A scalar word is already its own fixed-width serialization. -/
def wordBlockCode (B : ℕ) (hB : 0 < B) : SubexponentialSAT.StackEncoding.BlockCode (Word B) where
  width := B
  width_pos := hB
  block := Subtype.val
  length_block x := x.property
  injective_block := Subtype.val_injective

theorem flat_eq_encode {d B : ℕ} (hB : 0 < B) (x : Code (Word B) d) :
    flat x = SubexponentialSAT.StackEncoding.encodeDataStack (wordBlockCode B hB) (List.ofFn x) := by
  have aux (xs : List (Word B)) :
      (xs.map Subtype.val).flatten =
        SubexponentialSAT.StackEncoding.encodeDataStack (wordBlockCode B hB) xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa only [List.map_cons, List.flatten_cons,
        SubexponentialSAT.StackEncoding.encodeDataStack_cons, wordBlockCode] using congrArg (x.val ++ ·) ih
  change (List.ofFn (Subtype.val ∘ x)).flatten = _
  simpa only [List.map_ofFn] using aux (List.ofFn x)

theorem flat_injective {d B : ℕ} (hB : 0 < B) :
    Function.Injective (flat : Code (Word B) d → List Bool) := by
  intro x y h
  rw [flat_eq_encode hB, flat_eq_encode hB] at h
  exact List.ofFn_injective (SubexponentialSAT.StackEncoding.encodeDataStack_injective _ h)

def vectorBlockCode (d B : ℕ) (hd : 0 < d) (hB : 0 < B) :
    SubexponentialSAT.StackEncoding.BlockCode (Code (Word B) d) where
  width := d * B
  width_pos := Nat.mul_pos hd hB
  block := flat
  length_block := flat_length
  injective_block := flat_injective hB

variable (p t : ℕ) [Fact p.Prime]

omit [Fact (Nat.Prime p)] in
/-- Semantic equality of canonical base words is exact byte equality. -/
theorem word_eq_of_value (x y : ScalarCode p t)
    (hx : BinaryArithmetic.toNat x.val < p^t) (hy : BinaryArithmetic.toNat y.val < p^t)
    (h : wordValue p t x = wordValue p t y) : x = y := by
  apply Subtype.ext
  apply SubexponentialSAT.SubexpModulusConstruction.bits_eq_of_length_of_value _ _
    (x.property.trans y.property.symm)
  have hv := congrArg ZMod.val h
  simpa only [wordValue, ZMod.val_natCast, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy] using hv

theorem wordMul_canonical (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (x y : ScalarCode p t) :
    BinaryArithmetic.toNat (SubexponentialSAT.SubexpPreparedQuartic.wordMul p t M x y).1.val < p^t := by
  change BinaryArithmetic.toNat (mulBaseRun _ _ _ _).1 < _
  rw [mulBaseRun_value _ _ _ _ (by
    rw [M.value]; exact pow_pos (Fact.out : p.Prime).pos t) (by
    rw [M.value]; exact modulus_le_width p t), M.value]
  exact Nat.mod_lt _ (pow_pos (Fact.out : p.Prime).pos t)

/-- The actual prepared zero cache is the all-zero canonical word. -/
theorem prepareScalarCache_zero_canonical (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (ht : 0 < t) :
    BinaryArithmetic.toNat (prepareScalarCache p t M ht).1.zero.val < p^t := by
  change BinaryArithmetic.toNat (SubexponentialSAT.SubexpModulusConstruction.normalizeRun (baseWidth p t) []).1 < p^t
  rw [SubexponentialSAT.SubexpModulusConstruction.normalizeRun_value]
  · simpa [BinaryArithmetic.toNat] using pow_pos (Fact.out : p.Prime).pos t
  · simp [BinaryArithmetic.toNat]

/-- Every nonempty scalar sum is canonical even if its cached zero was not. -/
theorem sumRun_canonical (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : ScalarCache p t) (x : ScalarCode p t × ℕ)
    (xs : List (ScalarCode p t × ℕ)) :
    BinaryArithmetic.toNat (sumRun (scalarProgram p t M cache) (x :: xs)).1.val < p^t :=
  SubexponentialSAT.SubexpPreparedQuartic.wordAdd_canonical p t M _ _

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
