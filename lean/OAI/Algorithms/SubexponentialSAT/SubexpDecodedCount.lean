import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticEncoding
import OAI.Algorithms.SubexponentialSAT.PositiveWordProgram

namespace OAI.Algorithms

/-!
# Exact natural decoding of the first coefficient word

Equality in the residue ring is not equality of unreduced binary words.
The final routine reduces the first word once; its raw value then lies below
the modulus, so the proved count bound makes natural-number decoding exact.
-/

namespace SubexponentialSAT.SubexpDecodedCount

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (p μ : ℕ) [Fact p.Prime]

def decodeConstantRun (M : SubexpPreparedQuartic.Modulus p μ)
    (a : Quad (Word (baseWidth p μ))) : List Bool × ℕ :=
  let reduced := SubexpPreparedQuartic.wordAdd p μ M a.c0
    (SubexpPreparedQuartic.zeroWord p μ)
  (reduced.1.val, reduced.2 + baseWidth p μ)

omit [Fact (Nat.Prime p)] in
theorem decodeConstantRun_length (M : SubexpPreparedQuartic.Modulus p μ)
    (a : Quad (Word (baseWidth p μ))) :
    (decodeConstantRun p μ M a).1.length = baseWidth p μ :=
  (SubexpPreparedQuartic.wordAdd p μ M a.c0 (SubexpPreparedQuartic.zeroWord p μ)).1.property

theorem decodeConstantRun_canonical (M : SubexpPreparedQuartic.Modulus p μ)
    (a : Quad (Word (baseWidth p μ))) :
    BinaryArithmetic.toNat (decodeConstantRun p μ M a).1 < p^μ :=
  SubexpPreparedQuartic.wordAdd_canonical p μ M a.c0 (SubexpPreparedQuartic.zeroWord p μ)

theorem decodeConstantRun_residue (M : SubexpPreparedQuartic.Modulus p μ)
    (a : Quad (Word (baseWidth p μ))) :
    (BinaryArithmetic.toNat (decodeConstantRun p μ M a).1 : ZMod (p^μ)) = wordValue p μ a.c0 := by
  change wordValue p μ
    (SubexpPreparedQuartic.wordAdd p μ M a.c0 (SubexpPreparedQuartic.zeroWord p μ)).1 = _
  rw [SubexpPreparedQuartic.wordAdd_correct, SubexpPreparedQuartic.zeroWord_value, add_zero]

omit [Fact (Nat.Prime p)] in
theorem decodeConstantRun_cost (M : SubexpPreparedQuartic.Modulus p μ)
    (a : Quad (Word (baseWidth p μ))) :
    (decodeConstantRun p μ M a).2 ≤ scalarBudget p μ + baseWidth p μ :=
  Nat.add_le_add_right (SubexpPreparedQuartic.wordAdd_cost p μ M a.c0
    (SubexpPreparedQuartic.zeroWord p μ)) _

omit [Fact (Nat.Prime p)] in
/-- A bounded residue equality uniquely identifies the raw natural value. -/
theorem raw_eq_of_canonical (xs : List Bool) (n : ℕ)
    (hxs : BinaryArithmetic.toNat xs < p^μ) (hn : n < p^μ)
    (heq : (BinaryArithmetic.toNat xs : ZMod (p^μ)) = (n : ZMod (p^μ))) : BinaryArithmetic.toNat xs = n := by
  have hval := congrArg ZMod.val heq
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hxs, Nat.mod_eq_of_lt hn] using hval

/-- Equality to a natural scalar in the actual quartic quotient identifies
the zeroth base-ring coefficient, using the proved coordinate injection. -/
theorem first_residue_eq (hμ : 0 < μ) (c : Fin 4 → ZMod (p^μ))
    (a : Quad (Word (baseWidth p μ))) (n : ℕ)
    (hvalue : quotientDenote c (a.map (wordValue p μ)) =
      (n : LiftRing.Extension (QuarticSearch.poly c))) :
    wordValue p μ a.c0 = (n : ZMod (p^μ)) := by
  let _ : Fact (1 < p^μ) := ⟨SubexpQuarticEncoding.primePower_one_lt p μ hμ⟩
  have hscalar : quotientDenote c (⟨(n : ZMod (p^μ)), 0, 0, 0⟩ : Quad (ZMod (p^μ))) =
      (n : LiftRing.Extension (QuarticSearch.poly c)) := by
    rw [quotientDenote_const, map_natCast]
  have hcoords := SubexpQuarticEncoding.quotientDenote_injective c
    (hvalue.trans hscalar.symm)
  exact congrArg Quad.c0 hcoords

/-- Exact decoding needs both canonical output and the strict count bound. -/
theorem decodeConstantRun_correct (M : SubexpPreparedQuartic.Modulus p μ)
    (hμ : 0 < μ) (c : Fin 4 → ZMod (p^μ))
    (a : Quad (Word (baseWidth p μ))) (n : ℕ) (hn : n < p^μ)
    (hvalue : quotientDenote c (a.map (wordValue p μ)) =
      (n : LiftRing.Extension (QuarticSearch.poly c))) :
    BinaryArithmetic.toNat (decodeConstantRun p μ M a).1 = n := by
  apply raw_eq_of_canonical p μ _ n (decodeConstantRun_canonical p μ M a) hn
  rw [decodeConstantRun_residue]
  exact first_residue_eq p μ hμ c a n hvalue

theorem decodeConstantRun_positive_iff (M : SubexpPreparedQuartic.Modulus p μ)
    (hμ : 0 < μ) (c : Fin 4 → ZMod (p^μ))
    (a : Quad (Word (baseWidth p μ))) (n : ℕ) (hn : n < p^μ)
    (hvalue : quotientDenote c (a.map (wordValue p μ)) =
      (n : LiftRing.Extension (QuarticSearch.poly c))) :
    0 < BinaryArithmetic.toNat (decodeConstantRun p μ M a).1 ↔ 0 < n := by
  rw [decodeConstantRun_correct p μ M hμ c a n hn hvalue]

/-- When a caller already proves canonicality, no final reduction is needed. -/
theorem firstWord_correct (hμ : 0 < μ) (c : Fin 4 → ZMod (p^μ))
    (a : Quad (Word (baseWidth p μ))) (n : ℕ) (hn : n < p^μ)
    (hcanonical : BinaryArithmetic.toNat a.c0.val < p^μ)
    (hvalue : quotientDenote c (a.map (wordValue p μ)) =
      (n : LiftRing.Extension (QuarticSearch.poly c))) :
    BinaryArithmetic.toNat a.c0.val = n :=
  raw_eq_of_canonical p μ _ n hcanonical hn (first_residue_eq p μ hμ c a n hvalue)

/-- This version composes directly with the actual binary remainder program,
whose output may have extra leading zero bits. -/
theorem first_mod_eq (hμ : 0 < μ) (c : Fin 4 → ZMod (p^μ))
    (a : Quad (Word (baseWidth p μ))) (n : ℕ) (hn : n < p^μ)
    (hvalue : quotientDenote c (a.map (wordValue p μ)) =
      (n : LiftRing.Extension (QuarticSearch.poly c))) :
    BinaryArithmetic.toNat a.c0.val % p^μ = n := by
  have hval := congrArg ZMod.val (first_residue_eq p μ hμ c a n hvalue)
  simpa only [wordValue, ZMod.val_natCast, Nat.mod_eq_of_lt hn] using hval

theorem positive_decodeConstantRun (M : SubexpPreparedQuartic.Modulus p μ)
    (hμ : 0 < μ) (c : Fin 4 → ZMod (p^μ))
    (a : Quad (Word (baseWidth p μ))) (n : ℕ) (hn : n < p^μ)
    (hvalue : quotientDenote c (a.map (wordValue p μ)) =
      (n : LiftRing.Extension (QuarticSearch.poly c))) :
    PositiveWordProgram.positive (decodeConstantRun p μ M a).1 = true ↔ 0 < n := by
  rw [PositiveWordProgram.positive_iff,
    decodeConstantRun_correct p μ M hμ c a n hn hvalue]

end SubexponentialSAT.SubexpDecodedCount

end OAI.Algorithms
