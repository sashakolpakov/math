import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramScan

namespace OAI.Algorithms

/-! Three nested finite-control loops enumerate the H-adic multiplication
indices from runtime unary degree. Every entry callback is an actual trace. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan

open BitProgram StructuredCalls

def tripleState (base : Store) (regs : Fin 8 → Bool)
    (i j k : ℕ) (tail : List Bool) : Data :=
  ⟨regs,Function.update (Function.update (Function.update (Function.update base
    24 (List.replicate k true)) 25 (List.replicate i true))
    26 (List.replicate j true)) 22 tail⟩

theorem tableCommand_eval (base : Store) (entry : Cmd 8 41)
    (f : ℕ → ℕ → ℕ → List Bool) (n K : ℕ)
    (h37 : base 37 = List.replicate n true)
    (h24 : base 24 = []) (h25 : base 25 = [])
    (h26 : base 26 = []) (h38 : base 38 = [])
    (step : ∀ i, i < n → ∀ j, j < n → ∀ k, k < n → ∀ regs tail,
      ∃ cost rf, cost ≤ K ∧
        Eval entry cost (tripleState base regs i j k tail)
          (tripleState base rf i j k (f i j k ++ tail)))
    (regs : Fin 8 → Bool) (tail : List Bool) :
    ∃ cost rf, cost ≤ tableBudget n K ∧
      Eval (tableCommand entry) cost ⟨regs,Function.update base 22 tail⟩
        ⟨rf,Function.update base 22 (tableCells f n ++ tail)⟩ := by
  apply copyAndScan_eval base 37 24 22 38 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (copyAndScan 37 25 22 38 (copyAndScan 37 26 22 38 entry))
    (fun k => cells (fun i => cells (fun j => f i j k) n) n)
    (scanBudget n (scanBudget n K)) n h37 h24 h38
  intro k hk rk tk
  let bk := Function.update base 24 (List.replicate k true)
  have middle := copyAndScan_eval bk 37 25 22 38 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (copyAndScan 37 26 22 38 entry) (fun i => cells (fun j => f i j k) n)
    (scanBudget n K) n (by simp [bk,h37]) (by simp [bk,h25]) (by simp [bk,h38])
  apply middle
  intro i hi ri ti
  let bi := Function.update bk 25 (List.replicate i true)
  have inner := copyAndScan_eval bi 37 26 22 38 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) entry (fun j => f i j k) K n
    (by simp [bi,bk,h37]) (by simp [bi,bk,h26]) (by simp [bi,bk,h38])
  apply inner
  intro j hj rj tj
  exact step i hi j hj k hk rj tj

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan

end OAI.Algorithms
