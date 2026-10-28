import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramControl

namespace OAI.Algorithms

/-! Polynomial bounds for the actual outer tape operations. Arithmetic is
accounted for by its proved per-node primitive runtime K. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT SubexpCRTOuterProgram

theorem controllerBudget_mono {W J Q K W' J' Q' K' : ℕ}
    (hW : W ≤ W') (hJ : J ≤ J') (hQ : Q ≤ Q') (hK : K ≤ K') :
    controllerBudget W J Q K ≤ controllerBudget W' J' Q' K' := by
  unfold controllerBudget initializationBudget SubexpFactorCountSetup.countBudget
    transportCost cleanupBudget
  gcongr

theorem controllerBudget_le (W J Q K S : ℕ)
    (hW : W ≤ S) (hJ : J ≤ S) (hQ : Q ≤ S) :
    controllerBudget W J Q K ≤ S * K + 300 * (S + 1)^3 := by
  calc
    _ ≤ controllerBudget S S S K := controllerBudget_mono hW hJ hQ le_rfl
    _ ≤ _ := by
      unfold controllerBudget initializationBudget SubexpFactorCountSetup.countBudget
        transportCost cleanupBudget
      ring_nf
      omega

/-- A single compilation-return step is included in this bound. -/
theorem compiled_controller_cost {runtime W J Q K S : ℕ}
    (hr : runtime ≤ controllerBudget W J Q K)
    (hW : W ≤ S) (hJ : J ≤ S) (hQ : Q ≤ S) :
    runtime + 1 ≤ S * K + 300 * (S + 1)^3 + 1 :=
  Nat.add_le_add_right (hr.trans (controllerBudget_le W J Q K S hW hJ hQ)) 1

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
