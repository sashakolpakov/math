import OAI.Analysis.PDE.Concentration.Physical.LatticeChart
import OAI.Analysis.PDE.Concentration.Lattice.FluxPullback
import OAI.Analysis.PDE.Green.Physical.FluxFaces

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
  OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Topology

def physicalCellPeriod {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (j : Fin (d + 1)) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 :=
  (OAI.Analysis.PDE.Green.euclideanCoordinates c).symm
    (physicalCellLatticeMap c R (OAI.Analysis.PDE.Green.euclideanCoordinates c (OAI.Analysis.PDE.Dirichlet.coordinateVector (j.succ, 0))))

@[simp] theorem timeProjection_physicalCellPeriod {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (j : Fin (d + 1)) :
    OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 (physicalCellPeriod c R j) = 0 := by
  rw [physicalCellPeriod, physicalCellLatticeMap_timeProjection,
    ContinuousLinearEquiv.symm_apply_apply, OAI.Analysis.PDE.Green.timeProjection_coordinate_succ]

theorem physical_lattice_time_test_periodic {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ)
    (j : Fin (d + 1)) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    η (OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 (x + physicalCellPeriod c R j)) =
      η (OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 x) := by
  rw [map_add, timeProjection_physicalCellPeriod, add_zero]

/-- On the genuine rotated side-100 torus, the Piola normal fluxes cancel
on real faces. The remaining faces are outside the fiber or test support. -/
theorem physical_lattice_compatible_faces {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (H : ℝ)
    (r : (ℂ × (Option (Fin d) → ℂ)) → ℝ) (η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ)
    (hH : ∀ z ∈ tsupport η, ∀ s, -H < z (0, s) ∧ z (0, s) < H)
    (hbounded : ∀ x, OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 x ∈ tsupport η →
      r (OAI.Analysis.PDE.Green.fullPhysicalProjection d x) ≤ 0 → ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).2‖ ≤ 28)
    (F : (Fin (d + 2) × Fin 3) → OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ)
    (hperiod : ∀ p (j : Fin (d + 1)) x, F p (x + physicalCellPeriod c R j) = F p x)
    (hzero : ∀ x, OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 x ∉ tsupport η → ∀ p, F p x = 0) :
    CompatibleLatticeFaces c (physicalCellLatticeMap c R)
      (OAI.Analysis.PDE.Green.physicalTimeBoxLower c H) (OAI.Analysis.PDE.Green.physicalTimeBoxUpper c H)
      (fun x => r (OAI.Analysis.PDE.Green.fullPhysicalProjection d x)) F := by
  apply (compatibleLatticeFaces_iff_pullback _ _ _ _ _ _).mpr
  have hr : (fun x => r (OAI.Analysis.PDE.Green.fullPhysicalProjection d ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm
      (physicalCellLatticeMap c R (OAI.Analysis.PDE.Green.euclideanCoordinates c x))))) =
      (fun x => r (OAI.Analysis.PDE.Green.fullPhysicalProjection d x)) := by
    funext x
    rw [physicalCellLatticeMap_fullProjection, ContinuousLinearEquiv.symm_apply_apply]
  rw [hr]
  apply OAI.Analysis.PDE.Green.physical_time_box_compatible_faces c H r η hH hbounded
  · intro p j x
    exact pulledLatticeFlux_periodic c (physicalCellLatticeMap c R) F
      (OAI.Analysis.PDE.Dirichlet.coordinateVector (j.succ, 0)) (fun p x => hperiod p j x) p x
  · intro x hx p
    apply pulledLatticeFlux_zero
    intro q
    apply hzero _ _ q
    simpa only [physicalCellLatticeMap_timeProjection,
      ContinuousLinearEquiv.symm_apply_apply] using hx

theorem physical_lattice_secondGreen_faces {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (H : ℝ)
    (r : (ℂ × (Option (Fin d) → ℂ)) → ℝ) (η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ)
    (hH : ∀ z ∈ tsupport η, ∀ s, -H < z (0, s) ∧ z (0, s) < H)
    (hbounded : ∀ x, OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 x ∈ tsupport η →
      r (OAI.Analysis.PDE.Green.fullPhysicalProjection d x) ≤ 0 → ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).2‖ ≤ 28)
    (K : (Fin (d + 2) × Fin 3) → (Fin (d + 2) × Fin 3) → OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ)
    (u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ)
    (hK : ∀ p q j x, K p q (x + physicalCellPeriod c R j) = K p q x)
    (hu : ∀ j x, u (x + physicalCellPeriod c R j) = u x) :
    CompatibleLatticeFaces c (physicalCellLatticeMap c R)
      (OAI.Analysis.PDE.Green.physicalTimeBoxLower c H) (OAI.Analysis.PDE.Green.physicalTimeBoxUpper c H)
      (fun x => r (OAI.Analysis.PDE.Green.fullPhysicalProjection d x))
      (OAI.Analysis.PDE.Green.secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector K u (fun x => η (OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 x))) := by
  apply physical_lattice_compatible_faces c R H r η hH hbounded
  · intro p j x
    exact OAI.Analysis.PDE.Green.secondGreenFlux_periodic_add OAI.Analysis.PDE.Dirichlet.coordinateVector K u _ (physicalCellPeriod c R j)
      (fun p q => hK p q j) (hu j) (physical_lattice_time_test_periodic c R η j) p x
  · intro x hx p
    exact (OAI.Analysis.PDE.Green.secondGreenFlux_eventually_zero OAI.Analysis.PDE.Dirichlet.coordinateVector K u _ x
      (OAI.Analysis.PDE.Green.time_test_zero_off_tsupport hx)).self_of_nhds p

theorem physical_lattice_cofactor_faces {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (H : ℝ)
    (r : (ℂ × (Option (Fin d) → ℂ)) → ℝ) (η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ)
    (hH : ∀ z ∈ tsupport η, ∀ s, -H < z (0, s) ∧ z (0, s) < H)
    (hbounded : ∀ x, OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 x ∈ tsupport η →
      r (OAI.Analysis.PDE.Green.fullPhysicalProjection d x) ≤ 0 → ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).2‖ ≤ 28)
    (e : Fin 3 → Quaternion ℝ) (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ)
    (hB : ∀ j x, B (x + physicalCellPeriod c R j) = B x)
    (hu : ∀ j x, u (x + physicalCellPeriod c R j) = u x) (t : ℝ) :
    CompatibleLatticeFaces c (physicalCellLatticeMap c R)
      (OAI.Analysis.PDE.Green.physicalTimeBoxLower c H) (OAI.Analysis.PDE.Green.physicalTimeBoxUpper c H)
      (fun x => r (OAI.Analysis.PDE.Green.fullPhysicalProjection d x))
      (OAI.Analysis.PDE.Green.secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
        (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor (d + 2)
          (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)) p q)
        u (fun x => η (OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 x))) := by
  apply physical_lattice_secondGreen_faces c R H r η hH hbounded _ u _ hu
  intro p q j x
  rw [OAI.Analysis.PDE.Green.quaternionHessian_periodic_add e (fun y => B y + t * u y)
    (physicalCellPeriod c R j) (fun y => by rw [hB j y, hu j y])]

end OAI.Analysis.PDE.Concentration
