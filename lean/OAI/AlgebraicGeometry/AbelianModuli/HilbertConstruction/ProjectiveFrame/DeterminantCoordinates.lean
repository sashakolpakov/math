import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.HomogeneousCoordinates
import Mathlib.LinearAlgebra.Determinant

/-! # Determinant Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.DeterminantCoordinates

noncomputable section

/-! Replacing a frame column computes the corresponding coordinate.
The cleared frame coordinates are therefore actual products of minors
of the labeled point vectors in any fixed ambient basis. -/
open scoped BigOperators Classical
universe u v w
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable {κ : Type w} [Fintype κ]

theorem basis_det_update_coordinate (e b : Module.Basis κ R V) (i : κ) (w : V) :
    e.det (Function.update b i w) = e.det b * b.repr w i := by
  have h : e.det.toMultilinearMap.toLinearMap b i = e.det b • b.coord i := by
    apply b.ext
    intro j
    change e.det (Function.update b i (b j)) = e.det b * b.repr (b j) i
    by_cases hji : j = i
    · subst j
      simp only [Function.update_eq_self, Module.Basis.repr_self_apply, ite_true, mul_one]
    · rw [Module.Basis.repr_self_apply, ite_eq_right hji, mul_zero]
      exact e.det.map_eq_zero_of_eq _ (by simp [hji]) hji
  exact LinearMap.congr_fun h w

def projectiveFrameDeterminantCoordinates (e : Module.Basis κ R V)
    (b : κ → V) (v w : V) (i : κ) : R :=
  e.det (Function.update b i w) *
    ∏ j ∈ Finset.univ.erase i, e.det (Function.update b j v)

theorem projectiveFrameDeterminantCoordinates_eq
    (e b : Module.Basis κ R V) (v w : V) :
    projectiveFrameDeterminantCoordinates e b v w =
      (e.det b) ^ Fintype.card κ • HomogeneousCoordinates.projectiveFrameHomogeneousCoordinates b v w := by
  funext i
  simp only [projectiveFrameDeterminantCoordinates, basis_det_update_coordinate,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, HomogeneousCoordinates.projectiveFrameHomogeneousCoordinates, Pi.smul_apply, smul_eq_mul]
  have hcard : Fintype.card κ - 1 + 1 = Fintype.card κ :=
    Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨i⟩)
  have hp : e.det b * (e.det b) ^ (Fintype.card κ - 1) = (e.det b) ^ Fintype.card κ := by
    rw [mul_comm, ← pow_succ, hcard]
  calc
    _ = (e.det b * (e.det b) ^ (Fintype.card κ - 1)) *
        (b.repr w i * ∏ j ∈ Finset.univ.erase i, b.repr v j) := by ring
    _ = _ := by rw [hp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.DeterminantCoordinates
