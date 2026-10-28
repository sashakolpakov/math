import OAI.Analysis.PDE.Concentration.Lattice.FiberMap
import OAI.Analysis.PDE.Concentration.Lattice.FluxPullback

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

theorem physicalSpatialProjection_fiberEquiv {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ)) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    OAI.Analysis.PDE.Green.physicalSpatialProjection d (spatialFiberEquiv L y) = OAI.Analysis.PDE.Green.physicalSpatialProjection d y := by
  ext i
  simp only [OAI.Analysis.PDE.Green.physicalSpatialProjection_apply, spatialFiberEquiv_apply, spatialFiberChange]
  rfl

def spatialCellLatticeMap {d m : ℕ}
    (c : (Fin (d + 1) × Fin 3) ≃ Fin (m + 1))
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ)) :
    (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ) :=
  (OAI.Analysis.PDE.Green.euclideanCoordinates c).symm.trans ((spatialFiberEquiv L).trans (OAI.Analysis.PDE.Green.euclideanCoordinates c))

@[simp] theorem spatialCellLatticeMap_apply {d m : ℕ}
    (c : (Fin (d + 1) × Fin 3) ≃ Fin (m + 1))
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ)) (y : Fin (m + 1) → ℝ) :
    (OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (spatialCellLatticeMap c L y) =
      spatialFiberEquiv L ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm y) := by
  simp [spatialCellLatticeMap]

theorem spatialLattice_sublevel_image {d m : ℕ}
    (c : (Fin (d + 1) × Fin 3) ≃ Fin (m + 1))
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ)) (lo hi : Fin (m + 1) → ℝ)
    (r : (Option (Fin d) → ℂ) → ℝ) :
    euclideanLatticeCell c (spatialCellLatticeMap c L) lo hi ∩
        {x | r (OAI.Analysis.PDE.Green.physicalSpatialProjection d x) < 0} =
      spatialFiberEquiv L ''
        ((OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc lo hi) ∩ {x | r (OAI.Analysis.PDE.Green.physicalSpatialProjection d x) < 0}) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, heq⟩, hr⟩
    have hx : spatialFiberEquiv L ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm y) = x := by
      rw [← spatialCellLatticeMap_apply, heq, ContinuousLinearEquiv.symm_apply_apply]
    refine ⟨(OAI.Analysis.PDE.Green.euclideanCoordinates c).symm y, ⟨?_, ?_⟩, hx⟩
    · simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hy
    · change r (OAI.Analysis.PDE.Green.physicalSpatialProjection d x) < 0 at hr
      rw [← hx, physicalSpatialProjection_fiberEquiv] at hr
      exact hr
  · rintro ⟨y, ⟨hy, hr⟩, rfl⟩
    refine ⟨⟨OAI.Analysis.PDE.Green.euclideanCoordinates c y, hy, ?_⟩, ?_⟩
    · apply (OAI.Analysis.PDE.Green.euclideanCoordinates c).symm.injective
      rw [spatialCellLatticeMap_apply, ContinuousLinearEquiv.symm_apply_apply,
        ContinuousLinearEquiv.symm_apply_apply]
    · simpa only [Set.mem_ofPred_eq, physicalSpatialProjection_fiberEquiv] using hr

theorem physical_spatial_lattice_faces {d m : ℕ}
    (c : (Fin (d + 1) × Fin 3) ≃ Fin (m + 1))
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ))
    (r : (Option (Fin d) → ℂ) → ℝ)
    (hbounded : ∀ q, r q ≤ 0 → ‖q‖ ≤ 28)
    (F : (Fin (d + 1) × Fin 3) → OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 → ℝ)
    (hperiod : ∀ p j y, F p (y + spatialFiberEquiv L (OAI.Analysis.PDE.Dirichlet.coordinateVector (j, 0))) = F p y) :
    CompatibleLatticeFaces c (spatialCellLatticeMap c L)
      (OAI.Analysis.PDE.Green.physicalBoxLower (OAI.Analysis.PDE.Green.physicalOptionCoordinates c))
      (OAI.Analysis.PDE.Green.physicalBoxUpper (OAI.Analysis.PDE.Green.physicalOptionCoordinates c))
      (fun y => r (OAI.Analysis.PDE.Green.physicalSpatialProjection d y)) F := by
  apply (compatibleLatticeFaces_iff_pullback _ _ _ _ _ _).mpr
  have hr : (fun y => r (OAI.Analysis.PDE.Green.physicalSpatialProjection d ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm
      (spatialCellLatticeMap c L (OAI.Analysis.PDE.Green.euclideanCoordinates c y))))) =
      (fun y => r (OAI.Analysis.PDE.Green.physicalSpatialProjection d y)) := by
    funext y
    rw [spatialCellLatticeMap_apply, ContinuousLinearEquiv.symm_apply_apply,
      physicalSpatialProjection_fiberEquiv]
  rw [hr]
  apply OAI.Analysis.PDE.Green.physical_cell_compatible_faces c r hbounded
  intro p j y
  apply pulledLatticeFlux_periodic
  intro q x
  simpa only [spatialCellLatticeMap_apply, ContinuousLinearEquiv.symm_apply_apply] using hperiod q j x

end OAI.Analysis.PDE.Concentration
