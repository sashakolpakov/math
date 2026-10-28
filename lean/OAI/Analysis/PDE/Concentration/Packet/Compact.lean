import OAI.Analysis.PDE.Concentration.Packet.Cell

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped ContDiff Matrix Matrix.Norms.Elementwise

local instance {ι : Type*} [Fintype ι] : NormedAddCommGroup (Matrix ι ι (Quaternion ℝ)) :=
  inferInstanceAs (NormedAddCommGroup (ι → ι → Quaternion ℝ))
local instance {ι : Type*} [Fintype ι] : NormedSpace ℝ (Matrix ι ι (Quaternion ℝ)) :=
  inferInstanceAs (NormedSpace ℝ (ι → ι → Quaternion ℝ))

theorem continuous_spatialPacketEmbedding (d : ℕ) :
    Continuous (fun p : OAI.Analysis.Calculus.Current.SpatialSpace d × (Option (Fin d) → ℂ) =>
      spatialPacketEmbedding d p.1 p.2) := by
  simp only [spatialPacketEmbedding_eq_coordinates]
  change Continuous (fun p : OAI.Analysis.Calculus.Current.SpatialSpace d × (Option (Fin d) → ℂ) =>
    (physicalSpatialSplit d).symm (spatialPiCoordinates d p.1, p.2))
  exact (physicalSpatialSplit d).symm.continuous.comp
    (((spatialPiCoordinates d).continuous.comp continuous_fst).prodMk continuous_snd)

/-- Compact closed physical cell, in the exact coordinates of the Green integral. -/
theorem isCompact_packetClosedCell {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) :
    IsCompact ((physicalPacketSplit d) ⁻¹' (closedPhysicalSpatialCell R ×ˢ
      {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0})) := by
  have h := ((isCompact_closedPhysicalSpatialCell R).prod
    (OAI.Analysis.Calculus.Current.isCompact_physical_fiber_sublevel a τ ha ht 0 (by norm_num))).image
      (continuous_spatialPacketEmbedding d)
  convert h using 1
  ext y
  constructor
  · intro hy
    refine ⟨physicalPacketSplit d y, hy, ?_⟩
    dsimp only
    rw [← physicalPacketSplit_symm, MeasurableEquiv.symm_apply_apply]
  · rintro ⟨p, hp, rfl⟩
    change physicalPacketSplit d (spatialPacketEmbedding d p.1 p.2) ∈
      closedPhysicalSpatialCell R ×ˢ {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0}
    rw [← physicalPacketSplit_symm, MeasurableEquiv.apply_symm_apply]
    exact hp

theorem integrable_packet_weighted_physicalCell {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (ht : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖)
    {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 → ℝ}
    (hu : ContinuousOn u {y | spatialDefiningFunction d a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0}) :
    IntegrableOn (fun y => (-u y) *
      (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) 0 0).re)
      (spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
        OAI.Analysis.PDE.Green.physicalSpatialFiber d a (OAI.Analysis.PDE.Green.energyComplexTime z)) := by
  let S := (physicalPacketSplit d) ⁻¹' (closedPhysicalSpatialCell R ×ˢ
    {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (OAI.Analysis.PDE.Green.energyComplexTime z) q ≤ 0})
  have hS := isCompact_packetClosedCell R a (OAI.Analysis.PDE.Green.energyComplexTime z) ha ht
  have hp (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) (hy : y ∈ S) :
      spatialDefiningFunction d a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0 := by
    change physicalPacketSplit d y ∈ closedPhysicalSpatialCell R ×ˢ
      {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (OAI.Analysis.PDE.Green.energyComplexTime z) q ≤ 0} at hy
    rw [physicalPacketSplit_apply] at hy
    exact hy.2
  have huc : ContinuousOn u S := hu.mono (fun y hy => hp y hy)
  have hAc : ContinuousOn (fun y =>
      (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) 0 0).re) S := by
    intro y hy
    have hreg := OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a (OAI.Analysis.PDE.Green.energyComplexTime z) ha ht
      ((hp y hy).trans (show (0 : ℝ) ≤ 1 by norm_num))
    have hn : physicalToNullCurrentPoint d (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) ∈
        OAI.Analysis.Calculus.Current.currentNonzeroDomain d := by
      change (physicalToNullCurrentPoint d (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y)).2 none ≠ 0
      rw [physicalToNullCurrentPoint_fiber_imaginary]
      exact hreg.1
    have hc := (latticeRegularizedCurrent_contDiffAt R h a hh κ cR cI v _ hn).continuousAt
    have hf : Continuous (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z) :=
      (OAI.Analysis.PDE.Green.continuous_fiberEmbedding (d + 1) 3).comp (continuous_const.prodMk continuous_id)
    have htc : Continuous (OAI.Analysis.Calculus.Current.timeComponent (d := d)) := by
      unfold OAI.Analysis.Calculus.Current.timeComponent
      apply Continuous.div_const
      apply Quaternion.continuous_re.comp
      fun_prop
    have hpnull : Continuous (physicalToNullCurrentPoint d) := by
      unfold physicalToNullCurrentPoint
      fun_prop
    simp only [physicalLatticeCurrent_time_entry]
    exact (htc.continuousAt.comp (hc.comp (x := y)
      (f := fun y => physicalToNullCurrentPoint d (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y))
      (hpnull.comp hf).continuousAt)).continuousWithinAt
  apply ((huc.neg.mul hAc).integrableOn_compact (μ := volume) hS).mono_set
  rw [physicalPacketSplit_latticeCell]
  exact preimage_mono (Set.prod_mono subset_rfl (fun q hq =>
    show OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (OAI.Analysis.PDE.Green.energyComplexTime z) q ≤ 0 from
      (show OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (OAI.Analysis.PDE.Green.energyComplexTime z) q < 0 from hq).le))

end OAI.Analysis.PDE.Concentration
