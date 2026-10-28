import Mathlib

/-! # Perfect Central Quotient -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PerfectCentralQuotient

noncomputable section

section

/-! Normal subgroups of a perfect group with simple central quotient. -/

open scoped Classical
open Subgroup

variable {H : Type*} [Group H] [Group.IsPerfect H]

theorem normal_eq_top_of_sup_center (N : Subgroup H) [N.Normal]
    (hN : N ⊔ Subgroup.center H = ⊤) : N = ⊤ := by
  let q := QuotientGroup.mk' N
  have hn : N.map q = ⊥ := (Subgroup.map_eq_bot_iff N).mpr (by
    change N ≤ (QuotientGroup.mk' N).ker
    rw [QuotientGroup.ker_mk'])
  have hZ : (Subgroup.center H).map q = ⊤ := by
    have he := congrArg (Subgroup.map q) hN
    rw [Subgroup.map_sup, hn, bot_sup_eq,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective N)] at he
    exact he
  let : IsMulCommutative (⊤ : Subgroup (H ⧸ N)) := hZ ▸
    (inferInstance : IsMulCommutative ((Subgroup.center H).map q))
  let : IsMulCommutative (H ⧸ N) := IsMulCommutative.of_comm fun x y =>
    congrArg Subtype.val (mul_comm' (⟨x, Subgroup.mem_top x⟩ : (⊤ : Subgroup (H ⧸ N)))
      ⟨y, Subgroup.mem_top y⟩)
  exact QuotientGroup.subgroup_eq_top_of_subsingleton N inferInstance

theorem normal_le_center_or_eq_top [IsSimpleGroup (H ⧸ Subgroup.center H)]
    (N : Subgroup H) [N.Normal] : N ≤ Subgroup.center H ∨ N = ⊤ := by
  let q := QuotientGroup.mk' (Subgroup.center H)
  have hn : (N.map q).Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  rcases hn.eq_bot_or_eq_top with h | h
  · left
    have he := (Subgroup.map_eq_bot_iff N).mp h
    simpa only [q, QuotientGroup.ker_mk'] using he
  · right
    apply normal_eq_top_of_sup_center N
    have he := congrArg (Subgroup.comap q) h
    simpa only [Subgroup.comap_map_eq, Subgroup.comap_top, q, QuotientGroup.ker_mk'] using he

end

/-! Abstract normal-subgroup structure of SL₂ in characteristic zero,
using the proved simplicity of its projective quotient. -/

open scoped Classical MatrixGroups

variable {K : Type*} [Field K] [CharZero K]

theorem specialLinearTwo_perfect : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
  ⟨Matrix.SL2.commutator_eq_top
    (a := (2 : K)) (by norm_num) (by norm_num)⟩

omit [CharZero K] in
theorem specialLinearTwo_center_finite : Finite (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) :=
  Finite.of_injective (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := K) (0 : Fin 2))
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := K) (0 : Fin 2)).injective

theorem specialLinearTwo_normal_finite_or_top (N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K))
    [N.Normal] : Finite N ∨ N = ⊤ := by
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) := specialLinearTwo_perfect
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple' ⟨(2 : K), by norm_num, by norm_num⟩
  rcases normal_le_center_or_eq_top N with h | h
  · left
    let : Finite (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) := specialLinearTwo_center_finite
    exact Finite.of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)
  · exact Or.inr h

theorem specialLinearTwo_not_solvable : ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) := by
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) := specialLinearTwo_perfect
  let t : Matrix.SpecialLinearGroup (Fin 2) K := Matrix.SpecialLinearGroup.transvection zero_ne_one 1
  have ht : t ≠ 1 := by
    intro h
    have he := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K => g.val 0 1) h
    simp [t, Matrix.SpecialLinearGroup.transvection_coe] at he
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) K) := ⟨⟨t, 1, ht⟩⟩
  exact Group.IsPerfect.not_isSolvable _

end

end OAI.NumberTheory.Quaternion.Arithmetic.PerfectCentralQuotient
