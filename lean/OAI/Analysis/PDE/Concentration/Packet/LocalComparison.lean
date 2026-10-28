import OAI.Analysis.PDE.Concentration.Packet.LocalEnergy

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped ContDiff Topology Matrix.Norms.Elementwise ComplexOrder MatrixOrder

theorem actual_packet_energy_comparison_local {n m : ℕ} {ι : Type*} [Fintype ι]
    (c : (Fin (n + 3) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (lam : ℝ) (hlam : 0 < lam) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (ht : a < ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) (ht' : ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ < 4)
    {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) 3 → ℝ} (hu : PacketLocalSmooth (n + 1) a u)
    (huperiod : ∀ (j : Fin (n + 2)) x, u (x + physicalCellPeriod c R j) = u x)
    (huz : ∀ y, spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y = 0 →
      u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) = 0)
    (hu0 : ∀ y ∈ (spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
      OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z)), u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) ≤ 0)
    (hpos : ∀ y ∈ (spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
      OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z)),
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun y =>
        lam * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) y +
          u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)) y)).PosSemidef)
    (heq : ∀ y ∈ (spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
      OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z)),
      OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun y =>
        lam * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) y +
          u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)) y) =
            lam * (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re) :
    let X₀ := ∫ y in (spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
      OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z)),
      (-u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)) *
        (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re
    let F := OAI.Analysis.PDE.Green.setFiberCombinedEnergy OAI.Analysis.Calculus.Quaternion.threeSlots lam (physicalLatticeEnergyCell R a)
      (physicalLatticeCurrent R h a κ cR cI v) (fun x => lam * physicalBackground (n + 1) x) u z
    0 ≤ F ∧ ((n : ℝ) + 1) / ((n : ℝ) + 3) * X₀ ≤ F ∧ F ≤ X₀ := by

  obtain ⟨g, hg, hgp, hgu⟩ := exists_packet_local_extension c R ha hu huperiod
    (isCompact_singleton (x := z)) (fun w hw => by
      obtain rfl := Set.mem_singleton_iff.mp hw
      exact ⟨ht, ht'⟩)
  have hraw (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3) :
      OAI.Analysis.PDE.Green.physicalFullDefining (n + 1) a (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) =
        spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y := by
    simp only [OAI.Analysis.PDE.Green.physicalFullDefining, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber, spatialDefiningFunction,
      Function.comp_apply]
  have hsame (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3)
      (hy : spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0) :
      g =ᶠ[𝓝 (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)] u :=
    hgu _ (by simp only [OAI.Analysis.PDE.Green.timeProjection_fiberEmbedding, Set.mem_singleton_iff]) (by rwa [hraw])
  have hinside (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3)
      (hy : y ∈ spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
        OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z)) :
      spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0 := by
    rw [← hraw]
    apply (physicalLatticeEnergyCell_fiber_defining_neg R a z _).le
    rwa [physicalLatticeEnergyCell_fiber]
  have hH (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3)
      (hy : spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0) :
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun w =>
        lam * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w +
          g (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z w)) y =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun w =>
        lam * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w +
          u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z w)) y := by
    apply OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ
    have hc : Continuous (fun w => OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z w) :=
      (OAI.Analysis.PDE.Green.continuous_fiberEmbedding _ _).comp (continuous_const.prodMk continuous_id)
    filter_upwards [(hsame y hy).comp_tendsto hc.continuousAt] with w hw
    exact congrArg (fun t : ℝ => lam * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w + t) hw
  have hb := actual_packet_energy_comparison R h a hh ha κ cR cI v lam hlam z ht.le ht'.le
    (hg.of_le (by simp))
    (physicalCellPeriod_to_fiberPeriod c R (cell_period_of_latticePeriodic_full c R hgp) z)
    (fun y hy => (hsame y hy.le).eq_of_nhds.trans (huz y hy))
    (fun y hy => by rw [(hsame y (hinside y hy)).eq_of_nhds]; exact hu0 y hy)
    (fun y hy => by rw [hH y (hinside y hy)]; exact hpos y hy)
    (fun y hy => by rw [hH y (hinside y hy)]; exact heq y hy)
  dsimp only at hb ⊢
  have hF := packetCombinedEnergy_congr_germs R h a ha κ cR cI v OAI.Analysis.Calculus.Quaternion.threeSlots lam z ht.le
    (fun y hy => hsame y (by rwa [← hraw]))
  rw [hF] at hb
  have hX :
      (∫ y in spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
        OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z),
        (-g (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)) *
          (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re) =
      (∫ y in spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
        OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z),
        (-u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)) *
          (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re) := by
    apply setIntegral_congr_fun (by
      rw [physicalPacketSplit_latticeCell]
      exact ((isCompact_closedPhysicalSpatialCell R).measurableSet.prod
        (OAI.Analysis.PDE.Green.isOpen_physical_fiber a (OAI.Analysis.PDE.Green.energyComplexTime z) ha ht.le).measurableSet).preimage
          (physicalPacketSplit (n + 1)).measurable)
    intro y hy
    exact congrArg (fun t : ℝ => -t *
      (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re)
      (hsame y (hinside y hy)).eq_of_nhds
  rw [hX] at hb
  exact hb

end OAI.Analysis.PDE.Concentration
