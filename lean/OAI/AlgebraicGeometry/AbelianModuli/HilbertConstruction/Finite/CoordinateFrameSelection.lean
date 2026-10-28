import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Coordinate Frame Selection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoordinateFrameSelection

noncomputable section

/-! A finite configuration with fewer than one r-th of its points in
each of r coordinate hyperplanes has a point outside all of them. This
is the finite union estimate used to select a projective frame. -/
open scoped BigOperators Classical
universe u v w

theorem finite_small_sets_do_not_cover
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [Nonempty κ]
    (B : κ → Finset ι)
    (h : ∀ k, Fintype.card κ * (B k).card < Fintype.card ι) :
    ∃ j : ι, ∀ k, j ∉ B k := by
  classical
  by_contra hn
  push Not at hn
  have hcover : (Finset.univ : Finset ι) ⊆ Finset.univ.biUnion B := by
    intro j _
    obtain ⟨k, hk⟩ := hn j
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hk⟩
  have hcount : Fintype.card ι ≤ ∑ k, (B k).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hsum : Fintype.card κ * (∑ k, (B k).card) < Fintype.card κ * Fintype.card ι := by
    rw [Finset.mul_sum]
    calc
      (∑ k, Fintype.card κ * (B k).card) < ∑ _k : κ, Fintype.card ι :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun k _ => h k)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact (Nat.not_lt_of_ge (Nat.mul_le_mul_left (Fintype.card κ) hcount)) hsum

theorem basis_sparseFamily_exists_all_coordinates_ne_zero
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    {ι : Type w} {κ : Type v} [Fintype ι] [Fintype κ] [Nonempty κ]
    (b : Module.Basis κ K V) (v : ι → V)
    (h : ∀ k, Fintype.card κ * (Finset.univ.filter (fun j => b.repr (v j) k = 0)).card <
      Fintype.card ι) :
    ∃ j : ι, ∀ k, b.repr (v j) k ≠ 0 := by
  obtain ⟨j, hj⟩ := finite_small_sets_do_not_cover
    (fun k => Finset.univ.filter (fun j => b.repr (v j) k = 0)) h
  refine ⟨j, fun k hk => ?_⟩
  exact hj k (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hk⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoordinateFrameSelection
