import OAI.LinearAlgebra.Moore.Rank.Mixed.Definition
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Logic.Equiv.Fintype

noncomputable section
namespace OAI.LinearAlgebra.Moore

open scoped BigOperators

theorem mixedMoore_piecewise_card {m : ℕ}
    (B D : Matrix (Fin m) (Fin m) (Quaternion ℝ)) (s : Finset (Fin m)) :
    mixedMoore m (fun i => if i ∈ s then B else D) =
      mixedMoore m (fun i => if i.val < s.card then B else D) := by
  classical
  have hsm : s.card ≤ m := by simpa using s.card_le_univ
  let e₀ : Fin s.card ≃ {i : Fin m // i.val < s.card} :=
    { toFun := fun i => ⟨⟨i.val, lt_of_lt_of_le i.isLt hsm⟩, i.isLt⟩
      invFun := fun i => ⟨i.val.val, i.property⟩
      left_inv := fun i => by rfl
      right_inv := fun i => by rfl }
  have hc : Fintype.card {i : Fin m // i.val < s.card} = Fintype.card {i // i ∈ s} := by
    rw [← Fintype.card_congr e₀]
    simp
  let e := Fintype.equivOfCardEq hc
  let τ : Equiv.Perm (Fin m) := e.extendSubtype
  have ht (i : Fin m) : τ i ∈ s ↔ i.val < s.card := by
    by_cases hi : i.val < s.card
    · exact iff_of_true (e.extendSubtype_mem i hi) hi
    · exact iff_of_false (e.extendSubtype_not_mem i hi) hi
  have he := mixedMoore_comp_perm m (fun i => if i ∈ s then B else D) τ
  simp only [ht] at he
  exact he.symm

theorem mixedMoore_scaled_piecewise {m : ℕ}
    (B D : Matrix (Fin m) (Fin m) (Quaternion ℝ)) (s : Finset (Fin m)) (a b : ℝ) :
    mixedMoore m (fun i => if i ∈ s then b • B else a • D) =
      a ^ (m - s.card) * b ^ s.card *
        mixedMoore m (fun i => if i.val < s.card then B else D) := by
  classical
  have he : (fun i => if i ∈ s then b • B else a • D) =
      (fun i => (if i ∈ s then b else a) • (if i ∈ s then B else D)) := by
    funext i
    split <;> rfl
  rw [he, (mixedMoore m).map_smul_univ, smul_eq_mul, mixedMoore_piecewise_card]
  have hp : (∏ i : Fin m, if i ∈ s then b else a) = b ^ s.card * a ^ (m - s.card) := by
    rw [Finset.prod_ite]
    have hc : (Finset.univ.filter (fun i : Fin m => i ∉ s)) = Finset.univ \ s := by
      ext i
      simp
    simp [hc, Finset.card_sdiff_of_subset (Finset.subset_univ s)]
  rw [hp]
  ring

/-- Binomial expansion of the actual Moore determinant, with the `j`
background copies occupying the first `j` argument positions. -/
theorem mooreDet_linear_combination_mixed {m : ℕ}
    (B D : Matrix (Fin m) (Fin m) (Quaternion ℝ)) (a b : ℝ) :
    mooreDet m (a • D + b • B) =
      ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * a ^ (m - j) * b ^ j *
        mixedMoore m (fun i => if i.val < j then B else D) := by
  classical
  rw [add_comm, ← mixedMoore_const]
  change mixedMoore m ((fun _ => b • B) + (fun _ => a • D)) = _
  rw [(mixedMoore m).map_add_univ]
  have he (s : Finset (Fin m)) :
      mixedMoore m (s.piecewise (fun _ => b • B) (fun _ => a • D)) =
        a ^ (m - s.card) * b ^ s.card *
          mixedMoore m (fun i => if i.val < s.card then B else D) := by
    change mixedMoore m (fun i => if i ∈ s then b • B else a • D) = _
    exact mixedMoore_scaled_piecewise B D s a b
  simp_rw [he]
  rw [← Finset.powerset_univ, Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_powersetCard j Finset.univ
    (fun k => a ^ (m - k) * b ^ k *
      mixedMoore m (fun i => if i.val < k then B else D))]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem mooreDet_segment_mixed {m : ℕ}
    (B D : Matrix (Fin m) (Fin m) (Quaternion ℝ)) (t : ℝ) :
    mooreDet m (t • D + (1 - t) • B) =
      ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * t ^ (m - j) * (1 - t) ^ j *
        mixedMoore m (fun i => if i.val < j then B else D) :=
  mooreDet_linear_combination_mixed B D t (1 - t)

end OAI.LinearAlgebra.Moore
