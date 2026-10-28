import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramMiddle
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramCost

namespace OAI.Algorithms

/-! Polynomial majorants for the physical middle and outer traversal. The
native service costs can be substituted directly in these inequalities. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT SubexpCRTOuterProgram

theorem middleBudget_mono {Q J W Km Ka Kl Q' J' W' Km' Ka' Kl' : ℕ}
    (hQ : Q ≤ Q') (hJ : J ≤ J') (hW : W ≤ W')
    (hm : Km ≤ Km') (ha : Ka ≤ Ka') (hl : Kl ≤ Kl') :
    Middle.budget Q J W Km Ka Kl ≤ Middle.budget Q' J' W' Km' Ka' Kl' := by
  unfold Middle.budget CofactorOuter.budget Cofactor.includeBudget Local.budget
    Horner.budget HornerProgram.budget
  gcongr

theorem middleBudget_le (Q J W Km Ka Kl S : ℕ)
    (hQ : Q ≤ S) (hJ : J ≤ S) (hW : W ≤ S)
    (hm : Km ≤ S) (ha : Ka ≤ S) (hl : Kl ≤ S) :
    Middle.budget Q J W Km Ka Kl ≤ 2000 * (S + 1)^3 := by
  calc
    _ ≤ Middle.budget S S S S S S := middleBudget_mono hQ hJ hW hm ha hl
    _ ≤ _ := by
      unfold Middle.budget CofactorOuter.budget Cofactor.includeBudget Local.budget
        Horner.budget HornerProgram.budget
      ring_nf
      omega

theorem reconstructionBudget_le (Q J W Km Ka Kl S : ℕ)
    (hQ : Q ≤ S) (hJ : J ≤ S) (hW : W ≤ S)
    (hm : Km ≤ S) (ha : Ka ≤ S) (hl : Kl ≤ S) :
    controllerBudget W J Q (Middle.budget Q J W Km Ka Kl) + 1 ≤
      2300 * (S + 1)^4 + 1 := by
  have hmid := middleBudget_le Q J W Km Ka Kl S hQ hJ hW hm ha hl
  have houter := controllerBudget_le W J Q (Middle.budget Q J W Km Ka Kl) S hW hJ hQ
  have hmult := Nat.mul_le_mul_left S hmid
  nlinarith

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
