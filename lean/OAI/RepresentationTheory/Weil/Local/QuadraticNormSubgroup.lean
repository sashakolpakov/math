import OAI.RepresentationTheory.Weil.Local.QuadraticNormAt
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Quadratic Norm Subgroup -/

namespace OAI.RepresentationTheory.Weil.Local.QuadraticNormSubgroup.Construction

noncomputable section

/-! The nonzero sums of two squares form an open subgroup containing all squares. -/

open Set Filter
open scoped _root_.Topology

def quadraticNormSubgroup (k : Type*) [Field k] : Subgroup kˣ where
  carrier := {a | ∃ x y : k, x ^ 2 + y ^ 2 = a.val}
  one_mem' := ⟨1, 0, by simp⟩
  mul_mem' := by
    rintro a b ⟨x, y, hx⟩ ⟨u, v, hu⟩
    refine ⟨x * u - y * v, x * v + y * u, ?_⟩
    change _ = a.val * b.val
    rw [← hx, ← hu]
    ring
  inv_mem' := by
    rintro a ⟨x, y, hx⟩
    refine ⟨x / a.val, y / a.val, ?_⟩
    rw [Units.val_inv_eq_inv_val]
    rw [div_pow, div_pow, ← add_div, hx]
    field_simp

theorem square_mem_quadraticNormSubgroup {k : Type*} [Field k] (a : kˣ) :
    a ^ 2 ∈ quadraticNormSubgroup k := ⟨a.val, 0, by simp⟩

def squareUnitsSubgroup (k : Type*) [CommGroup k] : Subgroup k :=
  (powMonoidHom 2 : k →* k).range

theorem squareUnitsSubgroup_le_quadraticNormSubgroup {k : Type*} [Field k] :
    squareUnitsSubgroup kˣ ≤ quadraticNormSubgroup k := by
  rintro a ⟨b, rfl⟩
  exact square_mem_quadraticNormSubgroup b

theorem mem_squareUnitsSubgroup_iff {k : Type*} [Field k] (a : kˣ) :
    a ∈ squareUnitsSubgroup kˣ ↔ ∃ x : k, x ^ 2 = a.val := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.val, congrArg Units.val hb⟩
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      intro he
      exact a.ne_zero (by simpa [he] using hx.symm)
    refine ⟨Units.mk0 x hx0, ?_⟩
    apply Units.ext
    exact hx

theorem squareUnitsSubgroup_isOpen
    {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [CharZero k] :
    IsOpen (squareUnitsSubgroup kˣ : Set kˣ) := by
  apply Subgroup.isOpen_of_mem_nhds (g := (1 : kˣ))
  have h := (Units.continuous_val.continuousAt (x := (1 : kˣ))).preimage_mem_nhds
    (QuadraticNormAt.Construction.square_range_mem_nhds_one (k := k))
  apply Filter.mem_of_superset h
  intro a ha
  exact (mem_squareUnitsSubgroup_iff a).mpr ha

theorem quadraticNormSubgroup_isOpen
    {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [CharZero k] :
    IsOpen (quadraticNormSubgroup k : Set kˣ) := by
  apply Subgroup.isOpen_of_mem_nhds (g := (1 : kˣ))
  exact Filter.mem_of_superset
    (squareUnitsSubgroup_isOpen.mem_nhds (Subgroup.one_mem _))
    squareUnitsSubgroup_le_quadraticNormSubgroup

theorem localField_quadraticNormSubgroup_isOpen
    {k : Type} [NormedField k] [CompleteSpace k] [CharZero k]
    (hnd : ¬ DiscreteTopology k) : IsOpen (quadraticNormSubgroup k : Set kˣ) := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField k with hd | ⟨_, rfl⟩
  · exact (hnd hd).elim
  · exact quadraticNormSubgroup_isOpen

end

end OAI.RepresentationTheory.Weil.Local.QuadraticNormSubgroup.Construction
