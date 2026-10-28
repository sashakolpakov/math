import OAI.LinearAlgebra.Moore.Rank.Mixed.Growth
import OAI.LinearAlgebra.Moore.Rank.Mixed.Positive

noncomputable section
namespace OAI.LinearAlgebra.Moore

open scoped ComplexOrder

/-- More than `r` copies of a positive-semidefinite background of quaternion
rank at most `r` have zero mixed Moore determinant. -/
theorem mixedMoore_eq_zero_of_rank {m r j : ℕ}
    (B D : Matrix (Fin m) (Fin m) (Quaternion ℝ))
    (hB : (complexify B).PosSemidef) (hD : (complexify D).PosSemidef)
    (hr : QuaternionRankLE r B) (hrj : r < j) (hjm : j ≤ m) :
    mixedMoore m (fun i => if i.val < j then B else D) = 0 := by
  apply mixedMoore_eq_zero_of_rank_and_nonneg B D hB hD hr hrj hjm
  intro k hk
  apply mixedMoore_nonneg
  intro i
  split <;> assumption

end OAI.LinearAlgebra.Moore
