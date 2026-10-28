import OAI.NumberTheory.ArithmeticGroups.Lattices.BasisLift

/-! # Orthogonal Basis Lift -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalBasisLift.Construction

noncomputable section

section

/-! An orthogonal basis of the complement of a nonzero vector extends
to an orthogonal basis by adjoining that vector. -/

open _root_.Module

theorem perpendicularProjection_kernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : E) :
    (ProjectedLattice.Construction.perpendicularProjection v).toLinearMap.ker = Submodule.span ℝ {v} := by
  ext x
  change ProjectedLattice.Construction.perpendicularProjection v x = 0 ↔ _
  rw [ProjectedLattice.Construction.perpendicularProjection, Submodule.orthogonalProjectionOnto_eq_zero_iff,
    Submodule.orthogonal_orthogonal]

theorem exists_orthogonal_basis_lift
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) (hv : v ≠ 0) (b : Basis ι ℝ (Submodule.span ℝ ({v} : Set E))ᗮ)
    (hb : Pairwise (fun i j => inner ℝ (b i) (b j) = 0)) :
    ∃ B : Basis (Unit ⊕ ι) ℝ E,
      B (Sum.inl ()) = v ∧ (∀ i, B (Sum.inr i) = (b i).val) ∧
      Pairwise (fun i j => inner ℝ (B i) (B j) = 0) := by
  obtain ⟨B, hB0, hBi⟩ := BasisLift.Construction.basis_lift_cyclic_kernel (ProjectedLattice.Construction.perpendicularProjection v).toLinearMap v hv
    (perpendicularProjection_kernel v) b (fun i => (b i).val)
    (fun i => Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (b i))
  refine ⟨B, hB0, hBi, ?_⟩
  intro i j hij
  rcases i with u | i <;> rcases j with u' | j
  · exact (hij (congrArg Sum.inl (Subsingleton.elim u u'))).elim
  · cases u
    rw [hB0, hBi]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b j).property
  · cases u'
    rw [hBi, hB0]
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (b i).property
  · rw [hBi, hBi]
    exact hb (fun h => hij (congrArg Sum.inr h))

end

/-! Coordinates in an orthogonal lifted basis separate the first
vector coefficient from the coordinates in its orthogonal complement. -/

open _root_.Module
open scoped Classical

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem orthogonal_lift_coordinate_first
    (v : E) (b : Basis ι ℝ (Submodule.span ℝ ({v} : Set E))ᗮ)
    (B : Basis (Unit ⊕ ι) ℝ E) (hBi : ∀ i, B (Sum.inr i) = (b i).val)
    (x : (Submodule.span ℝ ({v} : Set E))ᗮ) : B.repr x.val (Sum.inl ()) = 0 := by
  have he : (B.coord (Sum.inl ())).comp (Submodule.span ℝ ({v} : Set E))ᗮ.subtype = 0 := by
    apply b.ext
    intro i
    change B.repr (b i).val (Sum.inl ()) = 0
    rw [← hBi]
    simp
  exact LinearMap.congr_fun he x

theorem orthogonal_lift_coordinate_rest
    (v : E) (b : Basis ι ℝ (Submodule.span ℝ ({v} : Set E))ᗮ)
    (B : Basis (Unit ⊕ ι) ℝ E) (hBi : ∀ i, B (Sum.inr i) = (b i).val)
    (x : (Submodule.span ℝ ({v} : Set E))ᗮ) (j : ι) :
    B.repr x.val (Sum.inr j) = b.repr x j := by
  have he : (B.coord (Sum.inr j)).comp (Submodule.span ℝ ({v} : Set E))ᗮ.subtype = b.coord j := by
    apply b.ext
    intro i
    change B.repr (b i).val (Sum.inr j) = b.repr (b i) j
    rw [← hBi]
    simp only [Basis.repr_self_apply, Sum.inr.injEq]
  exact LinearMap.congr_fun he x

theorem orthogonal_lift_fractional_first
    (v : E) (b : Basis ι ℝ (Submodule.span ℝ ({v} : Set E))ᗮ)
    (B : Basis (Unit ⊕ ι) ℝ E) (hB0 : B (Sum.inl ()) = v)
    (hBi : ∀ i, B (Sum.inr i) = (b i).val)
    (x : (Submodule.span ℝ ({v} : Set E))ᗮ) (c : ℝ) :
    B.repr (x.val + c • v) (Sum.inl ()) = c := by
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    orthogonal_lift_coordinate_first v b B hBi x, zero_add]
  rw [← hB0]
  simp

theorem orthogonal_lift_fractional_rest
    (v : E) (b : Basis ι ℝ (Submodule.span ℝ ({v} : Set E))ᗮ)
    (B : Basis (Unit ⊕ ι) ℝ E) (hB0 : B (Sum.inl ()) = v)
    (hBi : ∀ i, B (Sum.inr i) = (b i).val)
    (x : (Submodule.span ℝ ({v} : Set E))ᗮ) (c : ℝ) (j : ι) :
    B.repr (x.val + c • v) (Sum.inr j) = b.repr x j := by
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    orthogonal_lift_coordinate_rest v b B hBi x j]
  have hz : B.repr v (Sum.inr j) = 0 := by
    rw [← hB0]
    simp
  rw [hz, mul_zero, add_zero]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalBasisLift.Construction
