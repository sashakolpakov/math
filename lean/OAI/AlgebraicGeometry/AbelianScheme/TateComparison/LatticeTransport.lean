import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Local

/-! # Lattice Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LatticeTransport

noncomputable section

/-! Full lattices remain full under surjective linear maps and pullback
by linear isomorphisms. This includes the chosen-block projections. -/

variable {R K V W : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower R K W]

theorem isLattice_map_surjective (M : Submodule R V) [Submodule.IsLattice K M]
    (f : V →ₗ[K] W) (hf : Function.Surjective f) :
    Submodule.IsLattice K (M.map (f.restrictScalars R)) := by
  constructor
  · exact Submodule.IsLattice.fg.map _
  · rw [Submodule.map_coe]
    change Submodule.span K (f '' (M : Set V)) = ⊤
    rw [Submodule.span_image, Submodule.IsLattice.span_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hf

theorem isLattice_comap_equiv (M : Submodule R W) [Submodule.IsLattice K M]
    (e : V ≃ₗ[K] W) : Submodule.IsLattice K (M.comap (e.toLinearMap.restrictScalars R)) := by
  change Submodule.IsLattice K (M.comap (e.restrictScalars R).toLinearMap)
  rw [Submodule.comap_equiv_eq_map_symm]
  exact isLattice_map_surjective M e.symm.toLinearMap e.symm.surjective

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LatticeTransport
