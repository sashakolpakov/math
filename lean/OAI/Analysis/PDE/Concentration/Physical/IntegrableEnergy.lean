import OAI.Analysis.PDE.Concentration.IntegrableEnergy
import OAI.Analysis.PDE.Concentration.Packet.Compact

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Matrix _root_.MeasureTheory OAI.Analysis.PDE.Green OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped ContDiff Matrix.Norms.Elementwise ComplexOrder MatrixOrder

/-- Physical energy comparison for the literal packet current. Its fiber
integrability is proved; no global extension of the current is required. -/
theorem packet_combined_energy_comparison {n : ℕ} {ι : Type*} [Fintype ι]
    (R₀ : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (e : Fin 3 → Quaternion ℝ) (lam : ℝ) (hlam : 0 < lam)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (ht : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) (ht' : ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ≤ 4)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) 3 → ℝ}
    (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hBperiod : ∀ j y, B (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z (y + spatialFiberEquiv (sideHundredLattice (spatialFramePi R₀)) (OAI.Analysis.PDE.Dirichlet.coordinateVector (j, 0)))) =
      B (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y))
    (huperiod : ∀ j y, u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z (y + spatialFiberEquiv (sideHundredLattice (spatialFramePi R₀)) (OAI.Analysis.PDE.Dirichlet.coordinateVector (j, 0)))) =
      u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y))
    (huz : ∀ y, OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (OAI.Analysis.PDE.Green.energyComplexTime z)
        (OAI.Analysis.PDE.Green.physicalSpatialProjection (n + 1) y) = 0 → u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) = 0)
    (hu0 : ∀ y ∈ (spatialFiberEquiv (sideHundredLattice (spatialFramePi R₀)) ''
      OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z)),
      u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) ≤ 0)
    (hpos : ∀ y ∈ (spatialFiberEquiv (sideHundredLattice (spatialFramePi R₀)) ''
      OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z)),
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y =>
        B (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) + u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)) y)).PosSemidef)
    (hrank : ∀ y ∈ (spatialFiberEquiv (sideHundredLattice (spatialFramePi R₀)) ''
      OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z)),
      ∃ w : Fin (n + 2) → Quaternion ℝ,
        OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)) y = OAI.Analysis.Calculus.Quaternion.outer w)
    (heq : ∀ y ∈ (spatialFiberEquiv (sideHundredLattice (spatialFramePi R₀)) ''
      OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z)),
      OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y =>
        B (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) + u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)) y) =
          lam * (physicalLatticeCurrent R₀ h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re) :
    let X₀ := ∫ y in (spatialFiberEquiv (sideHundredLattice (spatialFramePi R₀)) ''
      OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z)),
      (-u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)) *
        (physicalLatticeCurrent R₀ h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re
    let F := OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R₀ a)
      (physicalLatticeCurrent R₀ h a κ cR cI v) B u z
    0 ≤ F ∧ ((n : ℝ) + 1) / ((n : ℝ) + 3) * X₀ ≤ F ∧ F ≤ X₀ := by
  let c : (Fin (n + 2) × Fin 3) ≃ Fin ((n * 3 + 5) + 1) :=
    finProdFinEquiv.trans (finCongr (by omega))
  obtain ⟨R, hR, hneg, hzero, hbound, hreg⟩ :=
    OAI.Analysis.PDE.Green.exists_physical_spatial_defining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) ha ht ht'
  let L := sideHundredLattice (spatialFramePi R₀)
  let M := spatialCellLatticeMap c L
  let r := fun y => R (OAI.Analysis.PDE.Green.physicalSpatialProjection (n + 1) y)
  let cp := OAI.Analysis.PDE.Green.physicalOptionCoordinates c
  let lo := OAI.Analysis.PDE.Green.physicalBoxLower cp
  let hi := OAI.Analysis.PDE.Green.physicalBoxUpper cp
  have hcell : (spatialFiberEquiv L '' OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z)) =
      euclideanLatticeCell c M lo hi ∩ {y | r y < 0} := by
    rw [OAI.Analysis.PDE.Green.physicalSpatialFiber_eq_cell c a (OAI.Analysis.PDE.Green.energyComplexTime z) ha ht ht' hneg]
    exact (spatialLattice_sublevel_image c L lo hi R).symm
  have hfiber : (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z) ⁻¹' physicalLatticeEnergyCell R₀ a =
      euclideanLatticeCell c M lo hi ∩ {y | r y < 0} :=
    (physicalLatticeEnergyCell_fiber R₀ a z).trans hcell
  have hface : CompatibleLatticeFaces c M lo hi r (fun p y => u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) *
      OAI.Analysis.PDE.Green.realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e
        (OAI.LinearAlgebra.Moore.mooreCofactor (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e
          (fun y => B (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) + u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)) y)) p q)
        (fun y => u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)) p y) := by
    apply physical_spatial_lattice_faces c L R hbound
    intro p j y
    exact OAI.Analysis.PDE.Green.cofactor_firstFlux_periodic_add e
      (fun y => B (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) + u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y))
      (fun y => u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)) (spatialFiberEquiv L (OAI.Analysis.PDE.Dirichlet.coordinateVector (j, 0)))
      (fun x => by rw [hBperiod j x, huperiod j x]) (huperiod j) p y
  have hm := integrable_packet_weighted_physicalCell R₀ h a hh ha κ cR cI v z ht
    (OAI.Analysis.PDE.Green.contDiff_fiberSection hu z).continuous.continuousOn
  rw [hcell] at hm
  have hc := setFiberCombinedEnergy_comparison_lattice_integrable e lam hlam c M lo hi
    (OAI.Analysis.PDE.Green.physicalBoxLower_le_upper cp) z
    ((hR.of_le (by norm_num)).comp (OAI.Analysis.PDE.Green.physicalSpatialProjection (n + 1)).contDiff) hfiber
    (physicalLatticeCurrent R₀ h a κ cR cI v) hB hu hm (fun y _ => hreg y)
    (fun y hy => huz y ((hzero _).mp hy)) hface
    (fun y hy => hu0 y (hcell.symm ▸ hy))
    (fun y hy => hpos y (hcell.symm ▸ hy))
    (fun y hy => hrank y (hcell.symm ▸ hy))
    (fun y hy => heq y (hcell.symm ▸ hy))
  dsimp only at hc ⊢
  rw [physicalLatticeEnergyCell_fiber] at hc
  refine ⟨?_, hc⟩
  apply le_trans (mul_nonneg (by positivity) ?_) hc.1
  have hS : MeasurableSet (spatialFiberEquiv L ''
      OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z)) := by
    rw [hcell]
    exact (measurableSet_euclideanLatticeCell c M lo hi).inter
      (isOpen_lt ((hR.of_le (by norm_num : (0 : ℕ∞ω) ≤ 3)).continuous.comp
        (OAI.Analysis.PDE.Green.physicalSpatialProjection (n + 1)).continuous) continuous_const).measurableSet
  apply setIntegral_nonneg hS
  intro y hy
  have hd := OAI.LinearAlgebra.Moore.mooreDet_nonneg_of_complexify_posSemidef _ (hpos y hy)
  rw [heq y hy] at hd
  exact mul_nonneg (neg_nonneg.mpr (hu0 y hy)) ((mul_nonneg_iff_of_pos_left hlam).mp hd)

end OAI.Analysis.PDE.Concentration
