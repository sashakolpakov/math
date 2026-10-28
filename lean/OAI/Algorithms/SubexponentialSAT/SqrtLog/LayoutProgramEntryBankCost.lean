import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramEntryBankRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

namespace OAI.Algorithms

/-! Uniform numerical bounds for the concrete entry program. The universal
type words affect the result, but no type-dependent search is charged here. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes RowSelectionProgram

variable {r Q : ℕ}

def integerLength (R W P D : ℕ) : ℕ :=
  R*LayoutProgramScalar.termGrowth (2*W+P)+D+1

def integerBudget (r Q A R W P D : ℕ) : ℕ :=
  MatrixExtendedEntryProgram.guardStageCost r Q 1 0 Q+
    LayoutSourceValuesProgram.Native.numeratorAllowance r Q A R W P+
    27*CollisionProgram.typeWidth r Q 1+
    9*(R*LayoutProgramScalar.termGrowth (2*W+P))+
    100*(R*LayoutProgramScalar.termGrowth (2*W+P)+D+1)^2+60

theorem integerLength_bound (R W P D : ℕ) (u y : UniversalType r Q 1) :
    IntegerEntry.lengthBound R W P u y+D+1 ≤ integerLength R W P D := by
  unfold IntegerEntry.lengthBound integerLength
  gcongr
  exact Nat.sub_le _ _

theorem integerLength_one (R W P D : ℕ) : 1 ≤ integerLength R W P D := by
  unfold integerLength
  omega

theorem integerBudget_bound (A R W P D : ℕ) (t : Fin Q)
    (u y : UniversalType r Q 1) :
    IntegerEntry.budget A R W P D t u y ≤ integerBudget r Q A R W P D := by
  have hn := LayoutSourceValuesProgram.Native.numerator_cost_le A R W P t u y
  have hg : MatrixExtendedEntryProgram.guardStageCost r Q 1 0 t.val ≤
      MatrixExtendedEntryProgram.guardStageCost r Q 1 0 Q := by
    unfold MatrixExtendedEntryProgram.guardStageCost
    gcongr
    exact t.isLt.le
  have hl : IntegerEntry.lengthBound R W P u y ≤ R*LayoutProgramScalar.termGrowth (2*W+P) := by
    unfold IntegerEntry.lengthBound
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  unfold IntegerEntry.budget integerBudget
  gcongr

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
