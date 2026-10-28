import OAI.RepresentationTheory.Theta.Geometric.Local.MatrixLattice

/-! # Principal Local Matrices -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Preserving the original integral reference lattice forces every
supplied local matrix to lie in the literal integral special-linear group. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.localMatrix_preserves_reference_span (g : D.RationalSU)
    (hg : ∀ x ∈ D.pel.reference.lattice, D.rationalLinear g x ∈ D.pel.reference.lattice)
    (v : Fin s × Bool) (x : Fin 3 → ℚ_[q]) (hx : x ∈ D.localReferenceLattice v) :
    (D.localMatrix v g).val.mulVec x ∈ D.localReferenceLattice v := by
  let f := (Matrix.SpecialLinearGroup.toLin' (D.localMatrix v g)).toLinearMap.restrictScalars ℤ_[q]
  change f x ∈ D.localReferenceLattice v
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    change (D.localMatrix v g).val.mulVec (fun i => D.localEmbedding v (u i)) ∈ D.localReferenceLattice v
    rw [D.localMatrix_reference_action]
    exact Submodule.subset_span ⟨_, hg u hu, rfl⟩
  | zero =>
    rw [map_zero]
    exact (D.localReferenceLattice v).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (D.localReferenceLattice v).add_mem hx hy
  | smul a x _ hx =>
    rw [map_smul]
    exact (D.localReferenceLattice v).smul_mem a hx

theorem Data.ActiveHeckeThetaData.localMatrix_integral_of_reference_lattice (hc : D.HasFiniteCoordinates) (g : D.RationalSU)
    (hg : ∀ x ∈ D.pel.reference.lattice, D.rationalLinear g x ∈ D.pel.reference.lattice)
    (v : Fin s × Bool) : D.localMatrix v g ∈ SphericalGU.Spherical.integralSL3 q := by
  apply (AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates.TestTransport.integralSL3_iff_preserves_vectors q _).mpr
  intro x hx
  have h := D.localMatrix_preserves_reference_span g hg v x
    ((hc.2.1 v).symm ▸ (Local.MatrixLattice.standardLocalLattice_mem_iff q x).mpr hx)
  rw [hc.2.1] at h
  exact (Local.MatrixLattice.standardLocalLattice_mem_iff q _).mp h

end

end OAI.RepresentationTheory.Theta.Geometric
