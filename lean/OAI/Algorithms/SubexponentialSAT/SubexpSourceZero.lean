import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSelectedConversions
import OAI.Algorithms.SubexponentialSAT.SubexpFlatAdd

namespace OAI.Algorithms

/-! The actual source initializer stores a canonical all-false zero. This
byte-level fact is stronger than the semantic zero field of `Prepared` and
justifies literal padding in the source-row interpreter. -/

namespace SubexponentialSAT.SubexpSourceZero

open SubexpLiftRing

private theorem normalize_empty (B : ℕ) :
    (SubexpModulusConstruction.normalizeRun B []).1 = List.replicate B false := by
  induction B with
  | zero => rfl
  | succ B ih => simp [SubexpModulusConstruction.normalizeRun, List.replicate_succ, ih]

theorem prepareZero_encode (p μ : ℕ) [Fact p.Prime] :
    SubexpFlatAdd.encode (SubexpPreparedQuartic.prepareZero p μ).1 =
      List.replicate (4 * baseWidth p μ) false := by
  simp only [SubexpFlatAdd.encode, SubexpFlatAdd.flatten, SubexpFlatAdd.quadWords,
    SubexpPreparedQuartic.prepareZero, SubexpPreparedQuartic.literalWordRun,
    List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, normalize_empty, ← List.replicate_add]
  congr 1
  omega

theorem initializeSelected_zero_encode (p D : ℕ) [Fact p.Prime]
    (primeBits : List Bool) (hvalue : BinaryArithmetic.toNat primeBits = p)
    (hwidth : primeBits.length = Nat.log 2 p + 1) :
    SubexpFlatAdd.encode
      (SubexpSelectedConversions.initializeSelected p D primeBits hvalue hwidth).zero =
        List.replicate (4 * baseWidth p (D + 1)) false :=
  prepareZero_encode p (D + 1)

end SubexponentialSAT.SubexpSourceZero

end OAI.Algorithms
