import OAI.Analysis.PDE.Concentration.Packet.Comparison

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem quaternionHessian_fiberEmbedding_at {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ} (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (hf : ContDiffAt ℝ 2 f (OAI.Analysis.PDE.Green.fiberEmbedding n s z y)) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun x => f (OAI.Analysis.PDE.Green.fiberEmbedding n s z x)) y =
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian e f (OAI.Analysis.PDE.Green.fiberEmbedding n s z y)).submatrix Fin.succ Fin.succ := by
  obtain ⟨g, hg, heq⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hf
  have hc : Continuous (fun x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s => OAI.Analysis.PDE.Green.fiberEmbedding n s z x) := by
    unfold OAI.Analysis.PDE.Green.fiberEmbedding
    fun_prop
  have hgeq : (fun x => g (OAI.Analysis.PDE.Green.fiberEmbedding n s z x)) =ᶠ[𝓝 y]
      (fun x => f (OAI.Analysis.PDE.Green.fiberEmbedding n s z x)) := heq.comp_tendsto hc.continuousAt
  rw [← OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ e hgeq,
    OAI.Analysis.PDE.Green.quaternionHessian_fiberEmbedding e hg, OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ e heq]

/-- The PDE written in physical spatial variables is exactly the spatial
block of the full three-slot quaternionic Hessian used by energy propagation. -/
theorem packetPotential_spatial_hessian_at {d : ℕ} (lam : ℝ)
    {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ}
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3)
    (hu : ContDiffAt ℝ 2 u (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y))
    (hy : physicalNullHeight d (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) ≠ 0) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun w =>
        lam * spatialBackgroundFunction d (OAI.Analysis.PDE.Green.energyComplexTime z) w +
          u (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z w)) y =
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun x => lam * physicalBackground d x + u x)
        (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y)).submatrix Fin.succ Fin.succ := by
  have hf : ContDiffAt ℝ 2 (fun x => lam * physicalBackground d x + u x)
      (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) :=
    (contDiffAt_const.mul ((contDiffAt_physicalBackground d _ hy).of_le (by simp))).add hu
  simpa only [physicalBackground_fiber] using quaternionHessian_fiberEmbedding_at OAI.Analysis.Calculus.Quaternion.threeSlots z y hf

theorem packetPotential_spatial_hessian {d : ℕ} (lam : ℝ)
    {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ} (hu : ContDiff ℝ 2 u)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3)
    (hy : physicalNullHeight d (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) ≠ 0) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun w =>
        lam * spatialBackgroundFunction d (OAI.Analysis.PDE.Green.energyComplexTime z) w +
          u (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z w)) y =
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun x => lam * physicalBackground d x + u x)
        (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y)).submatrix Fin.succ Fin.succ :=
  packetPotential_spatial_hessian_at lam z y hu.contDiffAt hy

theorem spatial_coordinateVector_eq_packetEmbedding {d : ℕ} (j : Fin (d + 1)) :
    (OAI.Analysis.PDE.Dirichlet.coordinateVector (j, (0 : Fin 3)) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) =
      spatialPacketEmbedding d (EuclideanSpace.single (finSuccEquiv d j) 1) 0 := by
  rw [spatialPacketEmbedding_eq_coordinates, spatialPiCoordinates_single]
  ext ⟨i, α⟩
  fin_cases α <;> simp [OAI.Analysis.PDE.Dirichlet.coordinateVector, OAI.Analysis.PDE.Green.physicalSpatialEmbedding_eq,
    OAI.Analysis.PDE.Green.spatialRealComplexEmbedding_apply, Pi.single_apply, eq_comm]

theorem fiberEmbedding_add_packetEmbedding_real {d : ℕ} (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) (v : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z (y + spatialPacketEmbedding d v 0) =
      OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y - physicalSpatialTranslate v := by
  rw [spatialPacketEmbedding_eq_coordinates]
  ext ⟨i, α⟩
  refine Fin.cases ?_ (fun i => ?_) i
  · fin_cases α <;> simp [OAI.Analysis.PDE.Green.fiberEmbedding_apply_zero, physicalSpatialTranslate_time,
      physicalSpatialTranslate_imaginary]
  · fin_cases α <;> simp [OAI.Analysis.PDE.Green.fiberEmbedding_apply_succ, OAI.Analysis.PDE.Green.physicalSpatialEmbedding_eq,
      OAI.Analysis.PDE.Green.spatialRealComplexEmbedding_apply, physicalSpatialTranslate_spatial,
      physicalSpatialTranslate_imaginary, spatialPiCoordinates_apply]

theorem physicalCellPeriod_to_fiberPeriod {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ}
    (hp : ∀ (j : Fin (d + 1)) x, u (x + physicalCellPeriod c R j) = u x)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (j : Fin (d + 1)) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    u (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z
      (y + spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) (OAI.Analysis.PDE.Dirichlet.coordinateVector (j, 0)))) =
        u (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) := by
  rw [spatial_coordinateVector_eq_packetEmbedding, spatialPacketEmbedding_lattice,
    fiberEmbedding_add_packetEmbedding_real]
  simpa only [physicalCellPeriod_eq, sub_eq_add_neg] using hp j (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y)

end OAI.Analysis.PDE.Concentration
