import OAI.Analysis.PDE.Concentration.Packet.LocalRegularity
import OAI.Analysis.PDE.Concentration.ActualEnergy

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff Matrix.Norms.Elementwise

theorem physicalLatticeEnergy_congr_germs {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ℝ) (ha : 0 < a)
    (e : Fin 3 → Quaternion ℝ) (lam : ℝ)
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → Matrix (Fin (d + 2)) (Fin (d + 2)) (Quaternion ℝ))
    (B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ)
    {u g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ} (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (ht : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖)
    (heq : ∀ y, OAI.Analysis.PDE.Green.physicalFullDefining d a (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) ≤ 0 →
      u =ᶠ[𝓝 (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y)] g) :
    OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a) A B u z =
      OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a) A B g z := by
  apply setIntegral_congr_fun (by
    rw [physicalLatticeEnergyCell_fiber, physicalPacketSplit_latticeCell]
    exact ((isCompact_closedPhysicalSpatialCell R).measurableSet.prod
      (OAI.Analysis.PDE.Green.isOpen_physical_fiber a (OAI.Analysis.PDE.Green.energyComplexTime z) ha ht).measurableSet).preimage
        (physicalPacketSplit d).measurable)
  intro y hy
  exact combinedEnergyDensity_congr_germ e lam rfl Filter.EventuallyEq.rfl
    (heq y (physicalLatticeEnergyCell_fiber_defining_neg R a z hy).le)

theorem packetCombinedEnergy_congr_germs {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (e : Fin 3 → Quaternion ℝ) (lam : ℝ)
    {u g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ} (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (ht : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖)
    (heq : ∀ y, OAI.Analysis.PDE.Green.physicalFullDefining d a (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) ≤ 0 →
      u =ᶠ[𝓝 (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y)] g) :
    OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a)
      (physicalLatticeCurrent R h a κ cR cI v) (fun x => lam * physicalBackground d x) u z =
    OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a)
      (physicalLatticeCurrent R h a κ cR cI v) (fun x => lam * physicalBackground d x) g z := by
  apply setIntegral_congr_fun (by
    rw [physicalLatticeEnergyCell_fiber, physicalPacketSplit_latticeCell]
    exact ((isCompact_closedPhysicalSpatialCell R).measurableSet.prod
      (OAI.Analysis.PDE.Green.isOpen_physical_fiber a (OAI.Analysis.PDE.Green.energyComplexTime z) ha ht).measurableSet).preimage
        (physicalPacketSplit d).measurable)
  intro y hy
  exact combinedEnergyDensity_congr_germ e lam rfl Filter.EventuallyEq.rfl
    (heq y (physicalLatticeEnergyCell_fiber_defining_neg R a z hy).le)

/-- The literal moving energy is smooth on the open annulus under local
solution regularity near its closed fibers. Smooth extensions are constructed
on compact time neighborhoods within the proof. -/
theorem contDiffOn_packetCombinedEnergy_local {d m : ℕ} {ι : Type*} [Fintype ι]
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (e : Fin 3 → Quaternion ℝ) (lam : ℝ)
    {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ} (hu : PacketLocalSmooth d a u)
    (hp : ∀ (j : Fin (d + 1)) x, u (x + physicalCellPeriod c R j) = u x) :
    ContDiffOn ℝ ∞ (OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a)
      (physicalLatticeCurrent R h a κ cR cI v) (fun x => lam * physicalBackground d x) u)
      (physicalEnergyAnnulus a) := by
  intro z hz
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_physicalEnergyAnnulus a).mem_nhds hz)
  have hrhalf : 0 < r / 2 := by positivity
  have hTsub : Metric.closedBall z (r / 2) ⊆ physicalEnergyAnnulus a := by
    intro w hw
    apply hrsub
    exact (Metric.mem_closedBall.mp hw).trans_lt (by linarith)
  obtain ⟨g, hg, hgp, hgu⟩ := exists_packet_local_extension c R ha hu hp
    (isCompact_closedBall z (r / 2)) (fun w hw => hTsub hw)
  have hgf : ContDiffOn ℝ ∞ (OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a)
      (physicalLatticeCurrent R h a κ cR cI v) (fun x => lam * physicalBackground d x) g)
      (physicalEnergyAnnulus a) :=
    (contDiffOn_packetCombinedEnergy R h a hh ha κ cR cI v e lam hg).mono (fun w hw => hw.1)
  apply ((hgf z hz).contDiffAt ((isOpen_physicalEnergyAnnulus a).mem_nhds hz)).congr_of_eventuallyEq
      ?_ |>.contDiffWithinAt
  filter_upwards [Metric.ball_mem_nhds z hrhalf] with w hw
  have hwT : w ∈ Metric.closedBall z (r / 2) := Metric.ball_subset_closedBall hw
  apply packetCombinedEnergy_congr_germs R h a ha κ cR cI v e lam w (hTsub hwT).1.le
  intro y hy
  exact (hgu _ (by rwa [OAI.Analysis.PDE.Green.timeProjection_fiberEmbedding]) hy).symm

end OAI.Analysis.PDE.Concentration
