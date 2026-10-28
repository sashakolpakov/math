import OAI.Analysis.PDE.Concentration.Physical.Extension
import OAI.Analysis.PDE.Concentration.Lattice.EnergySmooth
import OAI.Analysis.PDE.Concentration.Packet.Cell
import OAI.Analysis.PDE.Dirichlet.ComparisonLocal

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem combinedEnergyDensity_congr_germ {n s : ℕ} (e : Fin s → Quaternion ℝ) (lam : ℝ)
    {A A' : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ)}
    {B B' u u' : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ} {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s}
    (hA : A x = A' x) (hB : B =ᶠ[𝓝 x] B') (hu : u =ᶠ[𝓝 x] u') :
    OAI.Analysis.PDE.Green.combinedEnergyDensity e lam A B u x = OAI.Analysis.PDE.Green.combinedEnergyDensity e lam A' B' u' x := by
  have hH (t : ℝ) : OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B' y + t * u' y) x := by
    apply OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ
    filter_upwards [hB, hu] with y hBy huy
    rw [hBy, huy]
  simp only [OAI.Analysis.PDE.Green.combinedEnergyDensity, OAI.Analysis.PDE.Green.spatialPencilEnergyDensity, hH, hA, hu.eq_of_nhds]

theorem physicalLatticeEnergyCell_fiber_defining_neg {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    {y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3}
    (hy : y ∈ (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z) ⁻¹' physicalLatticeEnergyCell R a) :
    OAI.Analysis.PDE.Green.physicalFullDefining d a (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) < 0 := by
  rw [physicalLatticeEnergyCell_fiber, physicalPacketSplit_latticeCell] at hy
  change physicalPacketSplit d y ∈ closedPhysicalSpatialCell R ×ˢ
    {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (OAI.Analysis.PDE.Green.energyComplexTime z) q < 0} at hy
  rw [physicalPacketSplit_apply] at hy
  simpa only [OAI.Analysis.PDE.Green.physicalFullDefining, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber, Set.mem_ofPred_eq] using hy.2

theorem extendedPhysical_fields_eq_near_fiber {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (ht : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) {y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3}
    (hy : y ∈ (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z) ⁻¹' physicalLatticeEnergyCell R a) :
    extendedPhysicalLatticeCurrent R h a ha κ cR cI v =ᶠ[𝓝 (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y)]
      physicalLatticeCurrent R h a κ cR cI v ∧
    extendedPhysicalBackground d a ha =ᶠ[𝓝 (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y)]
      physicalBackground d := by
  apply extendedPhysical_fields_eq_near R h a ha κ cR cI v
  · simpa only [OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber] using ht
  · exact (physicalLatticeEnergyCell_fiber_defining_neg R a z hy).le

/-- The smooth extensions change neither term of the actual moving-fiber
energy. Equality holds without an integrability hypothesis. -/
theorem extendedPhysical_energy_eq {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (e : Fin 3 → Quaternion ℝ) (lam : ℝ)
    (u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (ht : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) :
    OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a)
      (extendedPhysicalLatticeCurrent R h a ha κ cR cI v)
      (fun x => lam * extendedPhysicalBackground d a ha x) u z =
    OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a)
      (physicalLatticeCurrent R h a κ cR cI v)
      (fun x => lam * physicalBackground d x) u z := by
  apply setIntegral_congr_fun (by
    rw [physicalLatticeEnergyCell_fiber, physicalPacketSplit_latticeCell]
    exact ((isCompact_closedPhysicalSpatialCell R).measurableSet.prod
      (OAI.Analysis.PDE.Green.isOpen_physical_fiber a (OAI.Analysis.PDE.Green.energyComplexTime z) ha ht).measurableSet).preimage
        (physicalPacketSplit d).measurable)
  intro y hy
  obtain ⟨hA, hB⟩ := extendedPhysical_fields_eq_near_fiber R h a ha κ cR cI v z ht hy
  apply combinedEnergyDensity_congr_germ e lam hA.eq_of_nhds _ Filter.EventuallyEq.rfl
  filter_upwards [hB] with x hx
  rw [hx]

/-- Smoothness of the literal packet energy, proved by extending only the
explicit current and background away from their irrelevant singular set. -/
theorem contDiffOn_packetCombinedEnergy {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (e : Fin 3 → Quaternion ℝ) (lam : ℝ)
    {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiffOn ℝ ∞ (OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a)
      (physicalLatticeCurrent R h a κ cR cI v) (fun x => lam * physicalBackground d x) u)
      {z | a < ‖OAI.Analysis.PDE.Green.energyComplexTime z‖} := by
  apply (contDiffOn_physicalLatticeCombinedEnergy R a ha e lam
    (contDiff_extendedPhysicalLatticeCurrent R h a hh ha κ cR cI v)
    (contDiff_const.mul (contDiff_extendedPhysicalBackground d a ha)) hu).congr
  intro z hz
  exact (extendedPhysical_energy_eq R h a ha κ cR cI v e lam u z hz.le).symm

end OAI.Analysis.PDE.Concentration
