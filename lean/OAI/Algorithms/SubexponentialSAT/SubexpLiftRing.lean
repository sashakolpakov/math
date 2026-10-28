import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ActualLiftRing
import OAI.Algorithms.SubexponentialSAT.ModularArithmetic
import OAI.Algorithms.SubexponentialSAT.StackEncoding

namespace OAI.Algorithms

/-!
# Uniform coefficient representations for the growing-parameter argument

Every base residue has an explicit little-endian word of width
`mu * (Nat.log 2 p + 1)`. The polynomial quotient uses one such word per
basis coefficient. These bounds keep p and mu visible. Binary modular
operations below use the existing bit/list algorithms and normalize back
to the prescribed width; their counters are source-level finite events,
not a claimed Turing-machine simulation.
-/

namespace SubexponentialSAT.SubexpLiftRing

open SubexponentialSAT.BinaryArithmetic

/-- Fixed-width little-endian binary expansion. -/
def fixedBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | B + 1, n => decide (n % 2 = 1) :: fixedBits B (n / 2)

@[simp] theorem fixedBits_length (B n : ℕ) : (fixedBits B n).length = B := by
  induction B generalizing n with
  | zero => rfl
  | succ B ih => simp [fixedBits, ih]

theorem bitVal_mod_two (n : ℕ) : bitVal (decide (n % 2 = 1)) = n % 2 := by
  have h := Nat.mod_lt n (by decide : 0 < 2)
  by_cases he : n % 2 = 1 <;> simp [bitVal, he] ; omega

theorem toNat_fixedBits (B n : ℕ) : BinaryArithmetic.toNat (fixedBits B n) = n % 2 ^ B := by
  induction B generalizing n with
  | zero => simp [fixedBits, Nat.mod_one]
  | succ B ih =>
      rw [fixedBits, toNat_cons, bitVal_mod_two, ih, pow_succ']
      exact Nat.mod_mul.symm

theorem toNat_fixedBits_of_lt (B n : ℕ) (hn : n < 2 ^ B) :
    BinaryArithmetic.toNat (fixedBits B n) = n := by rw [toNat_fixedBits, Nat.mod_eq_of_lt hn]

def baseWidth (p μ : ℕ) : ℕ := μ * (Nat.log 2 p + 1)

theorem modulus_le_width (p μ : ℕ) : p ^ μ ≤ 2 ^ baseWidth p μ := by
  calc
    p ^ μ ≤ (2 ^ (Nat.log 2 p + 1)) ^ μ :=
      Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_pow_succ_log_self Nat.one_lt_two p)) _
    _ = 2 ^ baseWidth p μ := by rw [← pow_mul]; congr 1; exact Nat.mul_comm _ _

section ResidueEncoding

variable (p μ : ℕ) [Fact p.Prime]

/-- Canonical binary encoding of a base coefficient. -/
def encodeBase (x : ZMod (p ^ μ)) : List Bool := fixedBits (baseWidth p μ) x.val

omit [Fact (Nat.Prime p)] in
@[simp] theorem encodeBase_length (x : ZMod (p ^ μ)) :
    (encodeBase p μ x).length = baseWidth p μ := fixedBits_length _ _

theorem encodeBase_value (x : ZMod (p ^ μ)) : BinaryArithmetic.toNat (encodeBase p μ x) = x.val :=
  toNat_fixedBits_of_lt _ _ (x.val_lt.trans_le (modulus_le_width p μ))

theorem encodeBase_injective : Function.Injective (encodeBase p μ) := by
  intro a b h
  have hv := congrArg BinaryArithmetic.toNat h
  simp only [encodeBase_value] at hv
  simpa using congrArg (fun n : ℕ => (n : ZMod (p ^ μ))) hv

/-- The fixed-width code also records the bounds needed for concatenation. -/
def baseCode (hμ : 0 < μ) : StackEncoding.BlockCode (ZMod (p ^ μ)) where
  width := baseWidth p μ
  width_pos := Nat.mul_pos hμ (Nat.zero_lt_succ _)
  block := encodeBase p μ
  length_block := encodeBase_length p μ
  injective_block := encodeBase_injective p μ

end ResidueEncoding

section QuotientEncoding

variable (p h μ : ℕ) [Fact p.Prime]

/-- The actual canonical quotient coordinates, in increasing degree order. -/
noncomputable def coefficientList (hμ : 0 < μ) (x : ActualLiftRing.Ring p h μ) :
    List (ZMod (p ^ μ)) :=
  List.ofFn ((LiftRing.coordinates (ActualLiftRing.F_monic p h μ hμ)) x)

theorem coefficientList_injective (hμ : 0 < μ) :
    Function.Injective (coefficientList p h μ hμ) := by
  intro a b hab
  exact (LiftRing.coordinates (ActualLiftRing.F_monic p h μ hμ)).injective
    (List.ofFn_injective hab)

/-- Binary storage of every quotient coefficient; no p-dependent alphabet. -/
noncomputable def encodeLambda (hμ : 0 < μ) (x : ActualLiftRing.Ring p h μ) : List Bool :=
  StackEncoding.encodeDataStack (baseCode p μ hμ) (coefficientList p h μ hμ x)

theorem encodeLambda_injective (hμ : 0 < μ) :
    Function.Injective (encodeLambda p h μ hμ) :=
  (StackEncoding.encodeDataStack_injective (baseCode p μ hμ)).comp
    (coefficientList_injective p h μ hμ)

theorem encodeLambda_length (hμ : 0 < μ) (hh : h ≠ 0)
    (x : ActualLiftRing.Ring p h μ) :
    (encodeLambda p h μ hμ x).length = h * (μ * (Nat.log 2 p + 1)) := by
  rw [encodeLambda, StackEncoding.length_encodeDataStack]
  simp only [coefficientList, List.length_ofFn, baseCode, baseWidth]
  rw [ActualLiftRing.F_degree p h μ hμ hh]

/-- Degree four stays fixed while both p and mu vary. -/
theorem encodeQuartic_length (hμ : 0 < μ) (x : ActualLiftRing.Ring p 4 μ) :
    (encodeLambda p 4 μ hμ x).length = 4 * (μ * (Nat.log 2 p + 1)) :=
  encodeLambda_length p 4 μ hμ (by decide) x

end QuotientEncoding

/-- Truncating high zero bits preserves any value already below the capacity. -/
theorem toNat_take_of_lt (B : ℕ) (xs : List Bool) (hx : BinaryArithmetic.toNat xs < 2 ^ B) :
    BinaryArithmetic.toNat (xs.take B) = BinaryArithmetic.toNat xs := by
  induction B generalizing xs with
  | zero => simpa using (Nat.eq_zero_of_le_zero (by simpa using hx)).symm
  | succ B ih =>
      cases xs with
      | nil => rfl
      | cons a xs =>
          have htail : BinaryArithmetic.toNat xs < 2 ^ B := by
            rw [toNat_cons, pow_succ] at hx
            omega
          simpa using congrArg (fun n => bitVal a + 2 * n) (ih xs htail)

/-- Bounded list operations restore the canonical output width. -/
def normalizeBits (B : ℕ) (xs : List Bool) : List Bool :=
  ModularArithmetic.padTo (List.replicate B false) (xs.take B)

@[simp] theorem normalizeBits_length (B : ℕ) (xs : List Bool) :
    (normalizeBits B xs).length = B := by simp [normalizeBits, ModularArithmetic.padTo_length]

theorem normalizeBits_value (B : ℕ) (xs : List Bool) (hx : BinaryArithmetic.toNat xs < 2 ^ B) :
    BinaryArithmetic.toNat (normalizeBits B xs) = BinaryArithmetic.toNat xs := by
  rw [normalizeBits, ModularArithmetic.padTo_correct]
  · exact toNat_take_of_lt B xs hx
  · simp only [List.length_replicate, List.length_take]
    exact Nat.min_le_left _ _

/-- Addition of encoded residues using only the already verified binary
arithmetic, binary division, and bounded list normalization. -/
def addBaseRun (B : ℕ) (modulus xs ys : List Bool) : List Bool × ℕ :=
  let out := ModularArithmetic.addModRun modulus xs ys
  (normalizeBits B out.1, out.2.length + 3 * B)

def mulBaseRun (B : ℕ) (modulus xs ys : List Bool) : List Bool × ℕ :=
  let out := ModularArithmetic.mulModRun modulus xs ys
  (normalizeBits B out.1, out.2.length + 3 * B)

theorem addBaseRun_value (B : ℕ) (modulus xs ys : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    BinaryArithmetic.toNat (addBaseRun B modulus xs ys).1 = (BinaryArithmetic.toNat xs + BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat modulus := by
  rw [addBaseRun, normalizeBits_value]
  · exact ModularArithmetic.addModRun_correct modulus xs ys hm
  · rw [ModularArithmetic.addModRun_correct modulus xs ys hm]
    exact (Nat.mod_lt _ hm).trans_le hcap

theorem mulBaseRun_value (B : ℕ) (modulus xs ys : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    BinaryArithmetic.toNat (mulBaseRun B modulus xs ys).1 = (BinaryArithmetic.toNat xs * BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat modulus := by
  rw [mulBaseRun, normalizeBits_value]
  · exact ModularArithmetic.mulModRun_correct modulus xs ys hm
  · rw [ModularArithmetic.mulModRun_correct modulus xs ys hm]
    exact (Nat.mod_lt _ hm).trans_le hcap

@[simp] theorem addBaseRun_length (B : ℕ) (m xs ys : List Bool) :
    (addBaseRun B m xs ys).1.length = B := by simp [addBaseRun]

@[simp] theorem mulBaseRun_length (B : ℕ) (m xs ys : List Bool) :
    (mulBaseRun B m xs ys).1.length = B := by simp [mulBaseRun]

/-- Uniform source-event bound, with one extra modulus bit allowed. -/
theorem addBaseRun_cost (B : ℕ) (m xs ys : List Bool)
    (hm : m.length ≤ B + 1) (hx : xs.length ≤ B) (hy : ys.length ≤ B) :
    (addBaseRun B m xs ys).2 ≤ 20 * (B + 2) ^ 2 + 3 * B := by
  exact Nat.add_le_add_right (ModularArithmetic.addModRun_count m xs ys (B + 1)
    hm (hx.trans (Nat.le_succ _)) (hy.trans (Nat.le_succ _))) _

theorem mulBaseRun_cost (B : ℕ) (m xs ys : List Bool)
    (hm : m.length ≤ B + 1) (hx : xs.length ≤ B) (hy : ys.length ≤ B) :
    (mulBaseRun B m xs ys).2 ≤ 200 * (B + 2) ^ 2 + 3 * B := by
  exact Nat.add_le_add_right (ModularArithmetic.mulModRun_count m xs ys (B + 1)
    hm (hx.trans (Nat.le_succ _)) (hy.trans (Nat.le_succ _))) _

end SubexponentialSAT.SubexpLiftRing

end OAI.Algorithms
