import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramInterval

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval

/-- The actual centered start is at most the number of evaluation nodes. -/
theorem intervalStart_le_Q (r Q R : ℕ) (hr : 0 < r) :
    Subexp.TailInterval.intervalStart r Q R ≤ Q := by
  rw [← SubexpIntervalStart.value_eq_intervalStart r Q R hr]
  have hd : 0 < 2*r := by omega
  change ((Q-1)*(r-1)-R*r)/(2*r) ≤ Q
  calc
    _ ≤ (Q*(2*r))/(2*r) := Nat.div_le_div_right
      ((Nat.sub_le _ _).trans (Nat.mul_le_mul (Nat.sub_le Q 1) (by omega)))
    _ = Q := Nat.mul_div_cancel Q hd

theorem cacheWidth_le_Q (r Q R : ℕ) (hr : 0 < r) :
    1+2*Subexp.TailInterval.intervalStart r Q R*R+Q ≤ 1+2*Q*R+Q := by
  gcongr
  exact intervalStart_le_Q r Q R hr

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval

end OAI.Algorithms
