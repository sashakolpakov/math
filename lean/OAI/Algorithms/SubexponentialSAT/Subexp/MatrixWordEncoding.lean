import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
import OAI.Algorithms.SubexponentialSAT.SubexpModulusConstruction

namespace OAI.Algorithms

/-! Canonical prime-field words for the local matrix checker. -/

namespace SubexponentialSAT.Subexp.MatrixWordEncoding

open BinaryArithmetic SubexpLiftRing

variable (p : ℕ) [Fact p.Prime]

def width : ℕ := baseWidth p 1

/-- The same fixed-bit encoding as `encodeBase` with exponent one, written
directly over `ZMod p` to avoid casts in the basis-checker interface. -/
def word (a : ZMod p) : List Bool := fixedBits (width p) a.val

omit [Fact p.Prime] in
@[simp] theorem word_length (a : ZMod p) : (word p a).length = width p :=
  fixedBits_length _ _

omit [Fact p.Prime] in
theorem modulus_capacity : p ≤ 2 ^ width p := by
  simpa only [width, pow_one] using modulus_le_width p 1

theorem word_value (a : ZMod p) : BinaryArithmetic.toNat (word p a) = a.val :=
  toNat_fixedBits_of_lt _ _ (a.val_lt.trans_le (modulus_capacity p))

theorem word_field_value (a : ZMod p) : (BinaryArithmetic.toNat (word p a) : ZMod p) = a := by
  rw [word_value]
  simp

theorem word_canonical (a : ZMod p) : BinaryArithmetic.toNat (word p a) < p := by
  rw [word_value]
  exact a.val_lt

theorem word_injective : Function.Injective (word p) := by
  intro a b hab
  have h := congrArg (fun bits => (BinaryArithmetic.toNat bits : ZMod p)) hab
  simpa only [word_field_value] using h

/-- A canonical machine output of the expected width is exactly the
corresponding field word, not merely a congruent numeric representative. -/
theorem word_unique (a : ZMod p) (bits : List Bool)
    (hl : bits.length = width p) (hc : BinaryArithmetic.toNat bits < p)
    (hv : (BinaryArithmetic.toNat bits : ZMod p) = a) : bits = word p a := by
  apply SubexpModulusConstruction.bits_eq_of_length_of_value
  · exact hl.trans (word_length p a).symm
  · calc
      BinaryArithmetic.toNat bits = (BinaryArithmetic.toNat bits : ZMod p).val := (ZMod.val_natCast_of_lt hc).symm
      _ = a.val := congrArg ZMod.val hv
      _ = BinaryArithmetic.toNat (word p a) := (word_value p a).symm

theorem words_unique (bits : List (List Bool)) (values : List (ZMod p))
    (hl : ∀ w ∈ bits, w.length = width p) (hc : ∀ w ∈ bits, BinaryArithmetic.toNat w < p)
    (hv : bits.map (fun w => (BinaryArithmetic.toNat w : ZMod p)) = values) :
    bits = values.map (word p) := by
  rw [← hv, List.map_map]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, Function.comp_apply]
    exact word_unique p _ _ (hl _ (List.getElem_mem hi)) (hc _ (List.getElem_mem hi)) rfl

def code : StackEncoding.BlockCode (ZMod p) where
  width := width p
  width_pos := by simp [width, baseWidth]
  block := word p
  length_block := word_length p
  injective_block := word_injective p

def modulus : List Bool := fixedBits (width p + 1) p

omit [Fact p.Prime] in
@[simp] theorem modulus_length : (modulus p).length = width p + 1 := fixedBits_length _ _

omit [Fact p.Prime] in
theorem modulus_value : BinaryArithmetic.toNat (modulus p) = p := by
  apply toNat_fixedBits_of_lt
  have hc := modulus_capacity p
  have hp : 0 < 2 ^ width p := pow_pos (by decide) _
  rw [pow_succ]
  omega

theorem modulus_positive : 0 < BinaryArithmetic.toNat (modulus p) := by
  rw [modulus_value]
  exact (Fact.out : p.Prime).pos

def zero : List Bool := word p 0

@[simp] theorem zero_length : (zero p).length = width p := word_length p 0

@[simp] theorem zero_value : BinaryArithmetic.toNat (zero p) = 0 := by
  rw [zero, word_value]
  simp

end SubexponentialSAT.Subexp.MatrixWordEncoding

end OAI.Algorithms
