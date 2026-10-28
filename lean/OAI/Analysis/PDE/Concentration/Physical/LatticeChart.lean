import OAI.Analysis.PDE.Concentration.Lattice.Scale
import OAI.Analysis.PDE.Concentration.Physical.Periodicity
import OAI.Analysis.PDE.Concentration.EuclideanLattice
import OAI.Analysis.PDE.Green.TimeTest

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

def spatialPiCoordinates (d : ℕ) : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] (Fin (d + 1) → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin d) => ℝ)).trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (d + 1) => ℝ) (finSuccEquiv d).symm)

@[simp] theorem spatialPiCoordinates_apply {d : ℕ} (y : OAI.Analysis.Calculus.Current.SpatialSpace d) (i : Fin (d + 1)) :
    spatialPiCoordinates d y i = y (finSuccEquiv d i) := by
  simp [spatialPiCoordinates, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft]

def spatialFramePi {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) :
    (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ) :=
  (spatialPiCoordinates d).symm.trans (R.trans (spatialPiCoordinates d))

@[simp] theorem spatialFramePi_apply {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (y : OAI.Analysis.Calculus.Current.SpatialSpace d) : spatialFramePi R (spatialPiCoordinates d y) = spatialPiCoordinates d (R y) := by
  simp [spatialFramePi]

theorem physicalLatticeEquiv_timeProjection {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ))
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 (physicalLatticeEquiv L x) = OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 x := by
  ext ⟨i, α⟩
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change physicalLatticeEquiv L x (0, α) = x (0, α)
  rw [physicalLatticeEquiv_apply]
  by_cases hα : α = 0
  · subst α
    exact spatialRealChange_time L _
  · exact spatialRealChange_other L _ _ _ hα

/-- The side-100 physical cell, in an arbitrary spatial frame, expressed
in the finite coordinates used by the Green identities. -/
def physicalCellLatticeMap {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) :
    (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ) :=
  (OAI.Analysis.PDE.Green.euclideanCoordinates c).symm.trans
    ((physicalLatticeEquiv (sideHundredLattice (spatialFramePi R))).trans (OAI.Analysis.PDE.Green.euclideanCoordinates c))

@[simp] theorem physicalCellLatticeMap_apply {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (x : Fin (m + 1) → ℝ) :
    (OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (physicalCellLatticeMap c R x) =
      physicalLatticeEquiv (sideHundredLattice (spatialFramePi R)) ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm x) := by
  simp [physicalCellLatticeMap]

theorem physicalCellLatticeMap_fullProjection {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (x : Fin (m + 1) → ℝ) :
    OAI.Analysis.PDE.Green.fullPhysicalProjection d ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (physicalCellLatticeMap c R x)) =
      OAI.Analysis.PDE.Green.fullPhysicalProjection d ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm x) := by
  rw [physicalCellLatticeMap_apply, fullPhysicalProjection_latticeEquiv]

theorem physicalCellLatticeMap_timeProjection {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (x : Fin (m + 1) → ℝ) :
    OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (physicalCellLatticeMap c R x)) =
      OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm x) := by
  rw [physicalCellLatticeMap_apply, physicalLatticeEquiv_timeProjection]

/-- The pullback of the weighted cutoff mass is exactly the existing unit
cell integrand: only the overall Jacobian changes. -/
theorem physicalCellLatticeMap_cutoff_weight {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (r : (ℂ × (Option (Fin d) → ℂ)) → ℝ)
    (η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ) (k : ℕ) (x : Fin (m + 1) → ℝ) :
    OAI.Analysis.PDE.Green.normalCutoffWeight (r (OAI.Analysis.PDE.Green.fullPhysicalProjection d
      ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (physicalCellLatticeMap c R x)))) k *
        ‖η (OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (physicalCellLatticeMap c R x)))‖ =
    OAI.Analysis.PDE.Green.normalCutoffWeight (r (OAI.Analysis.PDE.Green.fullPhysicalProjection d ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm x))) k *
        ‖η (OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm x))‖ := by
  rw [physicalCellLatticeMap_fullProjection, physicalCellLatticeMap_timeProjection]

end OAI.Analysis.PDE.Concentration
