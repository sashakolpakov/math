import OAI.Analysis.PDE.Concentration.Packet.LocalCylinder
import OAI.Analysis.PDE.Concentration.Packet.PeriodBasis

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped ContDiff Topology Matrix.Norms.Elementwise ComplexOrder MatrixOrder

def packetFullCoordinates (n : ℕ) : (Fin (n + 3) × Fin 3) ≃ Fin ((3 * n + 8) + 1) :=
  finProdFinEquiv.trans (finCongr (by omega))

def packetSpatialCoordinates (n : ℕ) : (Fin (n + 2) × Fin 3) ≃ Fin ((3 * n + 5) + 1) :=
  finProdFinEquiv.trans (finCongr (by omega))

/-- The concrete Dirichlet data needed by the concentration argument. This
record contains an actual smooth solution and its physical PDE, not an energy
or smoothing estimate. Existence of this record is a separate theorem. -/
structure PhysicalPacketSolution {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ) (lam : ℝ) where
  u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) 3 → ℝ
  smooth : PacketLocalSmooth (n + 1) a u
  periodic : ∀ (j : Fin (n + 2)) x,
    u (x + physicalCellPeriod (packetFullCoordinates n) R j) = u x
  nonpositive : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain (n + 1) a, u x ≤ 0
  boundary : ∀ x, (a < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ ∧
    ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ < 4) → OAI.Analysis.PDE.Green.physicalFullDefining (n + 1) a x = 0 → u x = 0
  admissible : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain (n + 1) a,
    (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
      (fun y => lam * physicalBackground (n + 1) y + u y) x).submatrix Fin.succ Fin.succ)).PosDef
  equation : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain (n + 1) a,
    OAI.LinearAlgebra.Moore.mooreDet (n + 2) ((OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
      (fun y => lam * physicalBackground (n + 1) y + u y) x).submatrix Fin.succ Fin.succ) =
        lam * (physicalLatticeCurrent R h a κ cR cI v x 0 0).re

variable {n : ℕ} {ι : Type*} [Fintype ι]
  {R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)}
  {h a : ℝ} {κ cR cI : ι → ℝ} {v : ι → Fin (n + 1) → ℝ} {lam : ℝ}

theorem fiberEmbedding_mem_propagationDomain {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3}
    (hz : z ∈ physicalEnergyAnnulus a) {y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3}
    (hy : spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0) :
    OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain (n + 1) a := by
  constructor
  · simpa only [OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber] using And.intro hz.1 hz.2
  · simpa only [OAI.Analysis.PDE.Green.physicalFullDefining, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber, spatialDefiningFunction,
      Function.comp_apply] using hy

theorem PhysicalPacketSolution.fiber_nonpositive
    (S : PhysicalPacketSolution R h a κ cR cI v lam)
    {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} (hz : z ∈ physicalEnergyAnnulus a)
    {y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3}
    (hy : spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0) :
    S.u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) ≤ 0 := by
  rcases hy.lt_or_eq with hy | hy
  · exact S.nonpositive _ (fiberEmbedding_mem_propagationDomain hz hy)
  · rw [S.boundary _ (by simpa only [OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber] using And.intro hz.1 hz.2)
      (by simpa only [OAI.Analysis.PDE.Green.physicalFullDefining, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber, spatialDefiningFunction,
        Function.comp_apply] using hy)]

theorem PhysicalPacketSolution.fiber_boundary
    (S : PhysicalPacketSolution R h a κ cR cI v lam)
    {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} (hz : z ∈ physicalEnergyAnnulus a)
    {y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3}
    (hy : spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y = 0) :
    S.u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) = 0 :=
  S.boundary _ (by simpa only [OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber] using And.intro hz.1 hz.2)
    (by simpa only [OAI.Analysis.PDE.Green.physicalFullDefining, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber, spatialDefiningFunction,
      Function.comp_apply] using hy)

theorem PhysicalPacketSolution.fiber_admissible
    (S : PhysicalPacketSolution R h a κ cR cI v lam) (ha : 0 < a)
    {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} (hz : z ∈ physicalEnergyAnnulus a)
    {y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3}
    (hy : spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0) :
    (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun w =>
      lam * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w +
        S.u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z w)) y)).PosDef := by
  have hd := fiberEmbedding_mem_propagationDomain hz hy
  rw [packetPotential_spatial_hessian_at lam z y
    ((S.smooth.contDiffAt hd.1 hd.2.le).of_le (by simp))
    (physicalNullHeight_ne_zero_on_domain ha hd)]
  exact S.admissible _ hd

theorem PhysicalPacketSolution.fiber_equation
    (S : PhysicalPacketSolution R h a κ cR cI v lam) (ha : 0 < a)
    {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} (hz : z ∈ physicalEnergyAnnulus a)
    {y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3}
    (hy : spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0) :
    OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun w =>
      lam * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w +
        S.u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z w)) y) =
          lam * (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re := by
  have hd := fiberEmbedding_mem_propagationDomain hz hy
  rw [packetPotential_spatial_hessian_at lam z y
    ((S.smooth.contDiffAt hd.1 hd.2.le).of_le (by simp))
    (physicalNullHeight_ne_zero_on_domain ha hd)]
  exact S.equation _ hd

theorem PhysicalPacketSolution.fiber_periodic
    (S : PhysicalPacketSolution R h a κ cR cI v lam) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (physicalSpatialSplit (n + 1)) (packetSpatialBasis R)
      (fun y => S.u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)) :=
  latticePeriodic_fiber_of_cell_period (packetFullCoordinates n) R S.periodic z

theorem PhysicalPacketSolution.fiber_smooth
    (S : PhysicalPacketSolution R h a κ cR cI v lam) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (hz : z ∈ physicalEnergyAnnulus a) :
    ContDiffOn ℝ ∞ (fun y => S.u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y))
      {y | spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0} := by
  intro y hy
  have ht : a < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)).1‖ ∧
      ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)).1‖ < 4 := by
    simpa only [OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber] using And.intro hz.1 hz.2
  have hr : OAI.Analysis.PDE.Green.physicalFullDefining (n + 1) a (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) ≤ 0 := by
    simpa only [OAI.Analysis.PDE.Green.physicalFullDefining, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber, spatialDefiningFunction,
      Function.comp_apply] using
      (show spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0 from hy)
  exact ((S.smooth.contDiffAt ht hr).comp y
    ((OAI.Analysis.PDE.Green.contDiff_fiberEmbedding (n + 2) 3 ∞).comp
      (contDiff_const.prodMk contDiff_id)).contDiffAt).contDiffWithinAt

theorem PhysicalPacketSolution.fiber_smooth_interior
    (S : PhysicalPacketSolution R h a κ cR cI v lam) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (hz : z ∈ physicalEnergyAnnulus a) :
    ContDiffOn ℝ ∞ (fun y => S.u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y))
      {y | spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0} :=
  (S.fiber_smooth z hz).mono (fun y hy =>
    show spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0 from
      (show spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 from hy).le)

theorem PhysicalPacketSolution.energy_comparison
    (S : PhysicalPacketSolution R h a κ cR cI v lam)
    (hh : 0 < h) (ha : 0 < a) (hlam : 0 < lam)
    {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} (hz : z ∈ physicalEnergyAnnulus a) :
    let X₀ := ∫ y in (spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
      OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z)),
      (-S.u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)) *
        (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re
    0 ≤ packetEnergy R h a κ cR cI v lam S.u z ∧
      ((n : ℝ) + 1) / ((n : ℝ) + 3) * X₀ ≤ packetEnergy R h a κ cR cI v lam S.u z ∧
      packetEnergy R h a κ cR cI v lam S.u z ≤ X₀ := by
  have hi (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3)
      (hy : y ∈ (spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
        OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z))) :
      spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 := by
    have hn := physicalLatticeEnergyCell_fiber_defining_neg R a z
      (y := y) (by rwa [physicalLatticeEnergyCell_fiber])
    simpa only [OAI.Analysis.PDE.Green.physicalFullDefining, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber, spatialDefiningFunction,
      Function.comp_apply] using hn
  exact actual_packet_energy_comparison_local (packetFullCoordinates n) R h a hh ha κ cR cI v
    lam hlam z hz.1 hz.2 S.smooth S.periodic
    (fun y hy => S.fiber_boundary hz hy)
    (fun y hy => S.fiber_nonpositive hz (hi y hy).le)
    (fun y hy => (S.fiber_admissible ha hz (hi y hy)).posSemidef)
    (fun y hy => S.fiber_equation ha hz (hi y hy))

end OAI.Analysis.PDE.Concentration
