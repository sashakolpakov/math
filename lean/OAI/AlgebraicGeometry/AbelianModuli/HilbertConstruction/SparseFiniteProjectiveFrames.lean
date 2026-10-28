import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoordinateFrameSelection
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Sparse Finite Projective Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseFiniteProjectiveFrames

noncomputable section

/-! The hyperplane sparsity bound supplies a spanning configuration,
a basis chosen among its vectors, and a further vector with every basis
coordinate nonzero. These are the linear data of a projective frame. -/
open scoped BigOperators Classical
universe u v
variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
variable {ι : Type v} [Fintype ι] (v : ι → V)
variable (hp : 0 < Module.finrank K V)
variable (hs : ∀ W : Submodule K V, W ≠ ⊤ →
  Module.finrank K V * (Finset.univ.filter (fun j => v j ∈ W)).card < Fintype.card ι)

include hp hs in
omit [Module.Finite K V] in
theorem sparseFiniteFamily_span : Submodule.span K (Set.range v) = ⊤ := by
  by_contra hn
  have h := hs (Submodule.span K (Set.range v)) hn
  have hall : Finset.univ.filter (fun j => v j ∈ Submodule.span K (Set.range v)) =
      (Finset.univ : Finset ι) := by
    apply Finset.filter_eq_self.mpr
    intro j _
    exact Submodule.subset_span (Set.mem_range_self j)
  rw [hall, Finset.card_univ] at h
  have hm : Fintype.card ι ≤ Module.finrank K V * Fintype.card ι := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (Fintype.card ι) (Nat.succ_le_of_lt hp)
  exact (Nat.not_lt_of_ge hm) h

include hp hs in
theorem sparseFiniteFamily_projectiveFrame :
    ∃ (κ : Type u) (_ : Fintype κ) (b : Module.Basis κ K V),
      Set.range b ⊆ Set.range v ∧ ∃ j : ι, ∀ k, b.repr (v j) k ≠ 0 := by
  classical
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := le_of_eq (sparseFiniteFamily_span v hp hs).symm
  let I : Set V := (linearIndepOn_empty K id).extend (Set.empty_subset (Set.range v))
  let b : Module.Basis I K V := Module.Basis.ofSpan hspan
  let : Finite I := Module.Finite.finite_basis b
  let : Fintype I := Fintype.ofFinite I
  have hcard : Fintype.card I = Module.finrank K V := (Module.finrank_eq_card_basis b).symm
  have : Nonempty I := Fintype.card_pos_iff.mp (hcard.symm ▸ hp)
  have hcoords (k : I) : Fintype.card I *
      (Finset.univ.filter (fun j => b.repr (v j) k = 0)).card < Fintype.card ι := by
    have hker : LinearMap.ker (b.coord k) ≠ ⊤ := by
      intro he
      have hm : b k ∈ LinearMap.ker (b.coord k) := he.symm ▸ Submodule.mem_top
      simp at hm
    have h := hs (LinearMap.ker (b.coord k)) hker
    simpa only [hcard, LinearMap.mem_ker, Module.Basis.coord_apply] using h
  exact ⟨I, inferInstance, b, Module.Basis.ofSpan_subset hspan,
    HilbertConstruction.Finite.CoordinateFrameSelection.basis_sparseFamily_exists_all_coordinates_ne_zero b v hcoords⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseFiniteProjectiveFrames
