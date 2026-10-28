import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectSAT

namespace OAI.Algorithms

/-! Fixed binary widths for every callback score, including failed trials. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

theorem cnf_mass_lt_binary_capacity {n m : ℕ}
    (C : Fin m → SAT.Clause (Fin n)) (rows : List (Row m)) :
    mass (cnfRowAccept C) (HashInput.violationWeight C) rows <
      2 ^ (n + Nat.size m + 1) := by
  apply initial_mass_lt_cap_power (cnfRowAccept C) (HashInput.violationWeight C) rows n m
  · simp [SAT.Assignment]
  · intro x
    simpa using HashInput.violationWeight_le C x

theorem cnf_acceptedCount_le {n m : ℕ}
    (C : Fin m → SAT.Clause (Fin n)) (rows : List (Row m)) :
    acceptedCount (cnfRowAccept C) rows ≤ 2 ^ n := by
  have h := mass_le (cnfRowAccept C) (fun _ => 1) rows 1 (fun _ => le_rfl)
  simpa [mass, acceptedCount, SAT.Assignment] using h

theorem cnf_acceptedCount_lt_binary_capacity {n m : ℕ}
    (C : Fin m → SAT.Clause (Fin n)) (rows : List (Row m)) :
    acceptedCount (cnfRowAccept C) rows < 2 ^ (n + 1) := by
  have h := cnf_acceptedCount_le C rows
  have hp : 0 < 2 ^ n := by positivity
  rw [pow_succ]
  omega

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
