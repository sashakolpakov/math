import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrapCost

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap


theorem totalCost_sizeDegreeBound {d Q : ℕ} (h : 3 ^ d ≤ 16 * (Q + 1)^2) :
    totalCost d ≤
      (preparationConstant * 16^4 + 531441 * 16^5 + 1) * (Q + 1)^10 := by
  have hprep := cost_sizeDegreeBound h
  have hscan := IrreducibleSearchCandidateControl.searchCost_sizeDegreeBound h
  have hp : (Q + 1)^8 ≤ (Q + 1)^10 := pow_le_pow_right₀ (by omega) (by decide)
  have h1 : 1 ≤ (Q + 1)^10 := Nat.one_le_pow _ _ (by omega)
  have hprep' := hprep.trans (Nat.mul_le_mul_left (preparationConstant * 16^4) hp)
  unfold totalCost
  calc
    _ ≤ (preparationConstant * 16^4) * (Q + 1)^10 +
        (531441 * 16^5) * (Q + 1)^10 + (Q + 1)^10 :=
      Nat.add_le_add (Nat.add_le_add hprep' hscan) h1
    _ = _ := by simp only [add_mul, one_mul]


end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
