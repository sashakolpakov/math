import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-! # Nil Submodule Unipotent Group -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.NilSubmoduleUnipotentGroup.Construction

noncomputable section

/-! A multiplicatively closed submodule consisting of nilpotent
elements defines a unipotent subgroup of the units. -/

open scoped Classical

variable {k A : Type*} [CommRing k] [Ring A] [Module k A]

theorem nilSubmodule_unit_inverse_sub_one_mem
    (W : Submodule k A) (hmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W)
    (hnil : ∀ x ∈ W, IsNilpotent x) (g : Aˣ) (hg : (g : A) - 1 ∈ W) :
    (↑g⁻¹ : A) - 1 ∈ W := by
  let x := -((g : A) - 1)
  have hx : x ∈ W := W.neg_mem hg
  obtain ⟨n, hn⟩ := hnil x hx
  let S := ∑ i ∈ Finset.range n, x ^ i
  have hprod : (g : A) * S = 1 := by
    have hgeom := mul_geom_sum x n
    have he : (g : A) = 1 - x := by dsimp [x]; abel
    rw [he]
    change (1 - x) * (∑ i ∈ Finset.range n, x ^ i) = 1
    rw [show 1 - x = -(x - 1) by abel, neg_mul, hgeom, hn]
    abel
  have hS : S = (↑g⁻¹ : A) := by
    calc
      S = (↑g⁻¹ : A) * ((g : A) * S) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [hprod, mul_one]
  have hxS : x * S ∈ W := by
    rw [show x * S = ∑ i ∈ Finset.range n, x ^ (i + 1) by
      simp only [S, Finset.mul_sum, pow_succ']]
    have hpow (i : ℕ) : x ^ (i + 1) ∈ W := by
      induction i with
      | zero => simpa only [zero_add, pow_one] using hx
      | succ i ih =>
        rw [pow_succ]
        exact hmul _ ih x hx
    exact W.sum_mem (fun i _ => hpow i)
  have he : (↑g⁻¹ : A) - 1 = x * S := by
    rw [← hS]
    have hgS : S - x * S = 1 := by
      have he : (g : A) = 1 - x := by dsimp [x]; abel
      simpa only [he, sub_mul, one_mul] using hprod
    exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hgS).trans (add_comm _ _))
  rwa [he]

def unipotentSubgroupOfNilSubmodule
    (W : Submodule k A) (hmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W)
    (hnil : ∀ x ∈ W, IsNilpotent x) : Subgroup Aˣ where
  carrier := {g | (g : A) - 1 ∈ W}
  one_mem' := by
    change (1 : A) - 1 ∈ W
    rw [sub_self]
    exact W.zero_mem
  mul_mem' {g h} hg hh := by
    change (g : A) * (h : A) - 1 ∈ W
    have he : (g : A) * (h : A) - 1 =
        ((g : A) - 1) * ((h : A) - 1) + ((g : A) - 1) + ((h : A) - 1) := by noncomm_ring
    rw [he]
    exact W.add_mem (W.add_mem (hmul _ hg _ hh) hg) hh
  inv_mem' {g} hg := nilSubmodule_unit_inverse_sub_one_mem W hmul hnil g hg

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.NilSubmoduleUnipotentGroup.Construction
