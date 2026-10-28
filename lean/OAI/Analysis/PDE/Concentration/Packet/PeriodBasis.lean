import OAI.Analysis.PDE.Concentration.Packet.Hessian

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Module Function OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

theorem latticePeriodic_of_basis_periods {E P V W ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {f : E → W}
    (hp : ∀ i, Periodic f (e.symm (b i, 0))) : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f := by
  have hall : ∀ p ∈ Submodule.span ℤ (range b), Periodic f (e.symm (p, 0)) := by
    intro p hp'
    induction hp' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hp i
    | zero =>
      intro x
      change f (x + e.symm 0) = f x
      rw [map_zero, add_zero]
    | add x y hx hy hpx hpy =>
      have he : e.symm (x + y, 0) = e.symm (x, 0) + e.symm (y, 0) := by
        rw [← map_add]
        simp
      rw [he]
      exact hpx.add_period hpy
    | smul a x hx hpx =>
      have he : e.symm (a • x, 0) = a • e.symm (x, 0) := by
        rw [← map_zsmul]
        simp
      rw [he]
      exact hpx.zsmul a
  intro x l
  have he : e.symm ((e x).1 + (l : P), (e x).2) = x + e.symm ((l : P), 0) := by
    apply e.injective
    simp only [map_add, ContinuousLinearEquiv.apply_symm_apply]
    apply Prod.ext <;> simp
  rw [he]
  exact hall l l.property x

def packetSpatialBasis {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) :
    Basis (Fin (d + 1)) ℝ (Fin (d + 1) → ℝ) :=
  (Pi.basisFun ℝ (Fin (d + 1))).map (sideHundredLattice (spatialFramePi R)).toLinearEquiv

theorem packetSpatialBasis_period {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (j : Fin (d + 1)) :
    (physicalSpatialSplit d).symm (packetSpatialBasis R j, 0) =
      spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) (OAI.Analysis.PDE.Dirichlet.coordinateVector (j, 0)) := by
  rw [spatial_coordinateVector_eq_packetEmbedding, spatialPacketEmbedding_eq_coordinates,
    spatialPiCoordinates_single, spatialFiberEquiv_physicalEmbedding,
    physicalSpatialSplit_symm]
  congr 1
  simp [packetSpatialBasis]

/-- Generator periodicity in the exact side-100 chart supplies the full
lattice-periodicity premise of the scalar comparison and input estimates. -/
theorem latticePeriodic_fiber_of_cell_period {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ}
    (hp : ∀ (j : Fin (d + 1)) x, u (x + physicalCellPeriod c R j) = u x)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (physicalSpatialSplit d) (packetSpatialBasis R)
      (fun y => u (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y)) := by
  apply latticePeriodic_of_basis_periods
  intro j
  rw [packetSpatialBasis_period]
  exact physicalCellPeriod_to_fiberPeriod c R hp z j

end OAI.Analysis.PDE.Concentration
