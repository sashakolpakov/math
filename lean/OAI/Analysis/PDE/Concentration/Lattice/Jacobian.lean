import OAI.Analysis.PDE.Concentration.Packet.Cell
import OAI.Analysis.PDE.Concentration.SpatialSplit
import OAI.Analysis.PDE.Concentration.Normalization

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

/-- The time/spatial decomposition as a genuine linear equivalence. -/
def timeSpatialSplit (n s : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s ≃ₗ[ℝ]
    (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s × OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) := {
    toEquiv := (OAI.Analysis.PDE.Green.timeSpaceEquiv n s).toEquiv
    map_add' := by
      intro x y
      change OAI.Analysis.PDE.Green.timeSpaceEquiv n s (x + y) = OAI.Analysis.PDE.Green.timeSpaceEquiv n s x + OAI.Analysis.PDE.Green.timeSpaceEquiv n s y
      apply Prod.ext
      · simp only [Prod.fst_add, OAI.Analysis.PDE.Green.timeSpaceEquiv_fst, map_add]
      · ext ⟨i, α⟩
        simp only [Prod.snd_add, PiLp.add_apply, OAI.Analysis.PDE.Green.timeSpaceEquiv_snd_apply]
    map_smul' := by
      intro c x
      change OAI.Analysis.PDE.Green.timeSpaceEquiv n s (c • x) = c • OAI.Analysis.PDE.Green.timeSpaceEquiv n s x
      apply Prod.ext
      · change (OAI.Analysis.PDE.Green.timeSpaceEquiv n s (c • x)).1 = c • (OAI.Analysis.PDE.Green.timeSpaceEquiv n s x).1
        simp only [OAI.Analysis.PDE.Green.timeSpaceEquiv_fst, map_smul]
      · ext ⟨i, α⟩
        change (OAI.Analysis.PDE.Green.timeSpaceEquiv n s (c • x)).2 (i, α) = c * (OAI.Analysis.PDE.Green.timeSpaceEquiv n s x).2 (i, α)
        simp only [PiLp.smul_apply, OAI.Analysis.PDE.Green.timeSpaceEquiv_snd_apply, smul_eq_mul]
  }

theorem timeSpatialSplit_symm (n s : ℕ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    (timeSpatialSplit n s).symm (z, y) = OAI.Analysis.PDE.Green.fiberEmbedding n s z y :=
  OAI.Analysis.PDE.Green.timeSpaceEquiv_symm_apply n s z y

theorem det_spatialFiberEquiv {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ)) :
    (spatialFiberEquiv L).toLinearEquiv.toLinearMap.det = L.toLinearEquiv.toLinearMap.det := by
  let e := physicalSpatialSplit d
  have he : e.toLinearEquiv.toLinearMap.comp
      ((spatialFiberEquiv L).toLinearEquiv.toLinearMap.comp e.toLinearEquiv.symm.toLinearMap) =
      LinearMap.prodMap L.toLinearEquiv.toLinearMap (LinearMap.id :
        (Option (Fin d) → ℂ) →ₗ[ℝ] (Option (Fin d) → ℂ)) := by
    apply LinearMap.ext
    rintro ⟨x, q⟩
    change e (spatialFiberEquiv L (e.symm (x, q))) = (L x, q)
    rw [show e.symm (x, q) = OAI.Analysis.PDE.Green.physicalSpatialEmbedding d x q from rfl,
      spatialFiberEquiv_physicalEmbedding]
    exact e.apply_symm_apply (L x, q)
  have hd := LinearMap.det_conj (spatialFiberEquiv L).toLinearEquiv.toLinearMap e.toLinearEquiv
  rw [he, LinearMap.det_prodMap, LinearMap.det_id, mul_one] at hd
  exact hd.symm

theorem det_physicalLatticeEquiv {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ)) :
    (physicalLatticeEquiv L).toLinearEquiv.toLinearMap.det = L.toLinearEquiv.toLinearMap.det := by
  let e := timeSpatialSplit (d + 1) 3
  have he : e.toLinearMap.comp
      ((physicalLatticeEquiv L).toLinearEquiv.toLinearMap.comp e.symm.toLinearMap) =
      LinearMap.prodMap (LinearMap.id : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 →ₗ[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
        (spatialFiberEquiv L).toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    rintro ⟨z, y⟩
    change e (physicalLatticeEquiv L (e.symm (z, y))) = (z, spatialFiberEquiv L y)
    rw [show e.symm (z, y) = OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y from timeSpatialSplit_symm _ _ _ _,
      physicalLatticeEquiv_fiberEmbedding]
    simpa only [e, timeSpatialSplit_symm] using e.apply_symm_apply (z, spatialFiberEquiv L y)
  have hd := LinearMap.det_conj (physicalLatticeEquiv L).toLinearEquiv.toLinearMap e
  rw [he, LinearMap.det_prodMap, LinearMap.det_id, one_mul, det_spatialFiberEquiv] at hd
  exact hd.symm

theorem det_sideHundred_spatialFrame {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) :
    (sideHundredLattice (spatialFramePi R)).toLinearEquiv.toLinearMap.det =
      (spatialCellMap R).toLinearMap.det := by
  let e := spatialPiCoordinates d
  have he : e.toLinearEquiv.toLinearMap.comp
      ((spatialCellMap R).toLinearMap.comp e.toLinearEquiv.symm.toLinearMap) =
      (sideHundredLattice (spatialFramePi R)).toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro y
    funext i
    change (e ((100 : ℝ) • R (e.symm y))) i = (100 : ℝ) * spatialFramePi R y i
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  have hd := LinearMap.det_conj (spatialCellMap R).toLinearMap e.toLinearEquiv
  rw [he] at hd
  exact hd

/-- The full cell Jacobian is exactly the spatial-cell Jacobian: time and
the transverse coordinates have identity blocks. This prevents a hidden
lattice-dependent loss in the concentration estimate. -/
theorem det_physicalCellLatticeMap {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) :
    (physicalCellLatticeMap c R).toLinearEquiv.toLinearMap.det =
      (spatialCellMap R).toLinearMap.det := by
  have hd := LinearMap.det_conj
    (physicalLatticeEquiv (sideHundredLattice (spatialFramePi R))).toLinearEquiv.toLinearMap
    (OAI.Analysis.PDE.Green.euclideanCoordinates c).toLinearEquiv
  change (physicalCellLatticeMap c R).toLinearEquiv.toLinearMap.det =
    (physicalLatticeEquiv (sideHundredLattice (spatialFramePi R))).toLinearEquiv.toLinearMap.det at hd
  exact hd.trans ((det_physicalLatticeEquiv _).trans (det_sideHundred_spatialFrame R))

theorem abs_det_physicalCellLatticeMap {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) :
    |(physicalCellLatticeMap c R).toLinearEquiv.toLinearMap.det| =
      volume.real (physicalSpatialCell R) := by
  rw [det_physicalCellLatticeMap, physicalSpatialCell_volume]

end OAI.Analysis.PDE.Concentration
