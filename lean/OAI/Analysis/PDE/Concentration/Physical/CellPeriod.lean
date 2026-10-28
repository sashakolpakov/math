import OAI.Analysis.PDE.Concentration.Physical.LatticeFaces
import OAI.Analysis.PDE.Concentration.Packet.Frequency

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

theorem spatialPiCoordinates_single {d : ℕ} (j : Fin (d + 1)) :
    spatialPiCoordinates d (EuclideanSpace.single (finSuccEquiv d j) 1) = Pi.single j 1 := by
  ext i
  simp [Pi.single_apply]

theorem physicalCellPeriod_eq {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (j : Fin (d + 1)) :
    physicalCellPeriod c R j =
      -physicalSpatialTranslate ((100 : ℝ) • R (EuclideanSpace.single (finSuccEquiv d j) 1)) := by
  have hv : (fun i : Fin (d + 1) =>
      (OAI.Analysis.PDE.Dirichlet.coordinateVector (j.succ, (0 : Fin 3)) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (i.succ, 0)) =
      Pi.single j 1 := by
    ext i
    simp [OAI.Analysis.PDE.Dirichlet.coordinateVector, Pi.single_apply, eq_comm]
  have hs : sideHundredLattice (spatialFramePi R) (Pi.single j 1) =
      spatialPiCoordinates d ((100 : ℝ) • R (EuclideanSpace.single (finSuccEquiv d j) 1)) := by
    rw [← spatialPiCoordinates_single, sideHundredLattice_apply, spatialFramePi_apply, map_smul]
  ext ⟨i, α⟩
  rw [physicalCellPeriod, physicalCellLatticeMap_apply, ContinuousLinearEquiv.symm_apply_apply,
    physicalLatticeEquiv_apply]
  by_cases hα : α = 0
  · subst α
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [OAI.Analysis.PDE.Dirichlet.coordinateVector, Fin.succ_ne_zero, eq_comm]
    · rw [spatialRealChange_spatial, hv, hs, spatialPiCoordinates_apply]
      simp
  · rw [spatialRealChange_other _ _ _ _ hα]
    simp [OAI.Analysis.PDE.Dirichlet.coordinateVector, physicalSpatialTranslate_imaginary _ _ _ hα, hα]

theorem physicalLatticeCurrent_physicalCellPeriod {d m : ℕ} {ι : Type*} [Fintype ι]
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (j : Fin (d + 1))
    (hfreq : ∀ k, ∃ l : ℤ, inner ℝ (packetSpatialFrequency (κ k) (v k))
      (R (EuclideanSpace.single (finSuccEquiv d j) 1)) = (l : ℝ) * (2 * Real.pi) / 100)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    physicalLatticeCurrent R h a κ cR cI v (x + physicalCellPeriod c R j) =
      physicalLatticeCurrent R h a κ cR cI v x := by
  rw [physicalCellPeriod_eq]
  have hp := physicalLatticeCurrent_periodic_of_dual_lattice R h a κ cR cI v
    (finSuccEquiv d j) hfreq
    (x - physicalSpatialTranslate ((100 : ℝ) • R (EuclideanSpace.single (finSuccEquiv d j) 1)))
  exact hp.symm.trans (congrArg (physicalLatticeCurrent R h a κ cR cI v) (sub_add_cancel x _))

end OAI.Analysis.PDE.Concentration
