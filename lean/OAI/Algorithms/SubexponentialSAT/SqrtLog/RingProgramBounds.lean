import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramWords

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgram

open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- The source-step bound of the fixed modular word machines. -/
def scalarMachineBudget (p t : ℕ) : ℕ := 6000 * (baseWidth p t + 1)^2

theorem scalarBudget_le_machineBudget (p t : ℕ) :
    scalarBudget p t ≤ scalarMachineBudget p t := by
  unfold scalarBudget scalarMachineBudget
  nlinarith [Nat.zero_le (baseWidth p t), Nat.zero_le ((baseWidth p t)^2)]

theorem scalarRing_machineBudget (p t : ℕ) [Fact p.Prime]
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t) (cache : ScalarCache p t) :
    ScalarBudget (scalarRing p t M cache) (scalarMachineBudget p t) := by
  have h := scalarRing_budget p t M cache
  have hb := scalarBudget_le_machineBudget p t
  exact ⟨h.zero.trans hb, h.one.trans hb,
    fun x y => (h.add x y).trans hb, fun x y => (h.mul x y).trans hb,
    fun x => (h.neg x).trans hb⟩

/-- Generic extension-ring callback counts, separately from flat scan time. -/
theorem represented_budget {C A R : Type*} [CommRing A] [CommRing R]
    (ops : RepresentedRing C A) (scalar : A →+* R) {d q : ℕ}
    (hq : ScalarBudget ops q) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → C) (zero one : Code C d)
    (htable hzero hone) :
    ScalarBudget (represented ops scalar basis table zero one htable hzero hone)
      (eventBudget d q) := by
  have h := program_budget ops.program hq.program table zero one
  exact ⟨h.zero, h.one, h.add, h.mul, h.neg⟩

theorem ternary_baseWidth (t : ℕ) : baseWidth 3 t = 2 * t := by
  have hlog : Nat.log 2 3 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  simp [baseWidth, hlog, Nat.mul_comm]

theorem ternary_scalarMachineBudget (t : ℕ) :
    scalarMachineBudget 3 t ≤ 24000 * (t + 1)^2 := by
  unfold scalarMachineBudget
  rw [ternary_baseWidth]
  nlinarith [Nat.zero_le t]

theorem ternary_extensionBudget (d t : ℕ) :
    eventBudget d (scalarMachineBudget 3 t) ≤ 72002 * (d + 1)^3 * (t + 1)^2 := by
  have he := eventBudget_polynomial d (scalarMachineBudget 3 t)
  have hs := ternary_scalarMachineBudget t
  have hq : 3 * scalarMachineBudget 3 t + 2 ≤ 72002 * (t + 1)^2 := by
    nlinarith [Nat.zero_le t]
  calc
    _ ≤ (d + 1)^3 * (3 * scalarMachineBudget 3 t + 2) := he
    _ ≤ (d + 1)^3 * (72002 * (t + 1)^2) := Nat.mul_le_mul_left _ hq
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
