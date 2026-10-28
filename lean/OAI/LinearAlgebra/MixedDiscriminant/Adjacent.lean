import OAI.LinearAlgebra.Moore.Rank.Mixed.Definition
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry

noncomputable section
namespace OAI.LinearAlgebra.MixedDiscriminant

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Replacing the next copy of `D` by `B` in a symmetric multilinear
expression inserts `D-B` into the first argument of the difference. -/
theorem symmetric_multilinear_adjacent {m : ℕ}
    (M : MultilinearMap ℝ (fun _ : Fin (m+1) => E) ℝ)
    (hsym : ∀ v (σ : Equiv.Perm (Fin (m+1))), M (fun i => v (σ i)) = M v)
    (B D : E) (j : ℕ) (hj : j < m+1) :
    M (fun i => if i.val < j then B else D) -
      M (fun i => if i.val < j+1 then B else D) =
      M (Fin.cons (D-B) (fun i : Fin m => if i.val < j then B else D)) := by
  let k : Fin (m+1) := ⟨j,hj⟩
  let σ : Equiv.Perm (Fin (m+1)) :=
    (finSuccEquiv m).trans (finSuccEquiv' k).symm
  have hσ0 : σ 0 = k := by simp [σ]
  have hσs (i : Fin m) : σ i.succ = k.succAbove i := by simp [σ]
  have hv0 : (fun i : Fin (m+1) => if (σ i).val < j then B else D) =
      Fin.cons D (fun i : Fin m => if i.val < j then B else D) := by
    funext i
    cases i using Fin.cases with
    | zero => simp [hσ0,k]
    | succ i =>
      rw [hσs]
      simp only [Fin.cons_succ]
      by_cases hi : i.val < j
      · rw [Fin.succAbove_of_castSucc_lt k i (show i.castSucc < k from hi)]
        simp [hi]
      · rw [Fin.succAbove_of_le_castSucc k i (show k ≤ i.castSucc from Nat.le_of_not_gt hi)]
        simp [hi, show ¬i.val+1 < j by omega]
  have hv1 : (fun i : Fin (m+1) => if (σ i).val < j+1 then B else D) =
      Fin.cons B (fun i : Fin m => if i.val < j then B else D) := by
    funext i
    cases i using Fin.cases with
    | zero => simp [hσ0,k]
    | succ i =>
      rw [hσs]
      simp only [Fin.cons_succ]
      by_cases hi : i.val < j
      · rw [Fin.succAbove_of_castSucc_lt k i (show i.castSucc < k from hi)]
        simp [hi, show i.val < j+1 by omega]
      · rw [Fin.succAbove_of_le_castSucc k i (show k ≤ i.castSucc from Nat.le_of_not_gt hi)]
        simp [hi]
  rw [← hsym (fun i => if i.val < j then B else D) σ, hv0,
    ← hsym (fun i => if i.val < j+1 then B else D) σ, hv1]
  have h := congrArg
    (fun L : MultilinearMap ℝ (fun _ : Fin m => E) ℝ =>
      L (fun i : Fin m => if i.val < j then B else D))
    (M.curryLeft.map_sub D B)
  simpa only [sub_apply, MultilinearMap.curryLeft_apply] using h.symm

end OAI.LinearAlgebra.MixedDiscriminant
namespace OAI.LinearAlgebra.Moore

theorem mixedMoore_adjacent {m : ℕ}
    (B D : Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ))
    (j : ℕ) (hj : j < m+1) :
    OAI.LinearAlgebra.Moore.mixedMoore (m+1) (fun i => if i.val < j then B else D) -
      OAI.LinearAlgebra.Moore.mixedMoore (m+1) (fun i => if i.val < j+1 then B else D) =
      OAI.LinearAlgebra.Moore.mixedMoore (m+1)
        (Fin.cons (D-B) (fun i : Fin m => if i.val < j then B else D)) :=
  OAI.LinearAlgebra.MixedDiscriminant.symmetric_multilinear_adjacent
    (OAI.LinearAlgebra.Moore.mixedMoore (m+1)) (OAI.LinearAlgebra.Moore.mixedMoore_comp_perm (m+1)) B D j hj

end OAI.LinearAlgebra.Moore
