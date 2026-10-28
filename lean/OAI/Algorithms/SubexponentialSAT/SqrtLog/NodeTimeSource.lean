import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorResourceSource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeUniform

namespace OAI.Algorithms

/-! The native integer-entry and column costs are polynomials in actual
retained source-word lengths, with the full incidence count preserved. -/
namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT Subexp SubexpLiftRing
open SubexponentialSAT.MulticolorTypes LayoutProgram LeafHeadSetupProgram
open LeafHeadSetupProgram.Bounds

private theorem integer_diagonal (X : ℕ) :
    EntryBank.integerBudget X X X X X X X ≤ 10000000000000*(X+1)^5 := by
  have hp (j : ℕ) (hj : j ≤ 5) : X^j ≤ (X+1)^5 :=
    (Nat.pow_le_pow_left (Nat.le_succ X) j).trans (Nat.pow_le_pow_right (by omega) hj)
  have h0 : 1 ≤ (X+1)^5 := by simpa using hp 0 (by decide)
  have h1 : X ≤ (X+1)^5 := by simpa using hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  dsimp only [EntryBank.integerBudget,LayoutProgramScalar.termGrowth,
    LayoutSourceValuesProgram.Native.numeratorAllowance,LayoutSourceValuesProgram.Native.scalarAllowance,
    MatrixExtendedEntryProgram.guardStageCost,MatrixEntryProgram.scanStageCost,CollisionProgram.typeWidth,
    LayoutProgramScalar.FromCounts.binomialCost,LayoutProgramScalar.numeratorPrepareCost,
    LayoutProgramScalar.numeratorFoldCost,UniversalRowMismatchTypes.extractBudget]
  norm_num only [Fin.val_zero]
  conv_lhs => ring_nf
  omega

theorem integerBudget_le (r Q A R W P D X : ℕ)
    (hr : r ≤ X) (hQ : Q ≤ X) (hA : A ≤ X) (hR : R ≤ X)
    (hW : W ≤ X) (hP : P ≤ X) (hD : D ≤ X) :
    EntryBank.integerBudget r Q A R W P D ≤ 10000000000000*(X+1)^5 := by
  apply le_trans _ (integer_diagonal X)
  dsimp only [EntryBank.integerBudget, LayoutProgramScalar.termGrowth,
    LayoutSourceValuesProgram.Native.numeratorAllowance, LayoutSourceValuesProgram.Native.scalarAllowance,
    MatrixExtendedEntryProgram.guardStageCost, MatrixEntryProgram.scanStageCost, CollisionProgram.typeWidth,
    LayoutProgramScalar.FromCounts.binomialCost, LayoutProgramScalar.numeratorPrepareCost,
    LayoutProgramScalar.numeratorFoldCost, UniversalRowMismatchTypes.extractBudget, LayoutProgramScalar.termGrowth]
  gcongr

/-- The diagonal uses the encoded width, not the coefficient magnitude. -/
theorem integerLength_le (R W P D X : ℕ) (hR : R ≤ X) (hW : W ≤ X) (hP : P ≤ X) (hD : D ≤ X) :
    EntryBank.integerLength R W P D ≤ 100*(X+1)^2 := by
  unfold EntryBank.integerLength LayoutProgramScalar.termGrowth
  nlinarith [Nat.mul_le_mul hR (Nat.add_le_add (Nat.mul_le_mul_left 28 hW) (Nat.mul_le_mul_left 14 hP))]

end SubexponentialSAT.SqrtLog.NodeTime

end OAI.Algorithms
