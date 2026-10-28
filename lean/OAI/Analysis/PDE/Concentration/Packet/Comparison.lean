import OAI.Analysis.PDE.Concentration.ExtendedCurrentFacts
import OAI.Analysis.PDE.Concentration.Physical.IntegrableEnergy

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped ContDiff Topology Matrix.Norms.Elementwise ComplexOrder MatrixOrder

theorem physicalBackground_fiber (d : ℕ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    physicalBackground d (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) =
      spatialBackgroundFunction d (OAI.Analysis.PDE.Green.energyComplexTime z) y := by
  simp only [physicalBackground, physicalToNullCurrentPoint_imaginary,
    OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber, spatialBackgroundFunction, Function.comp_apply]

theorem extendedPhysicalBackground_spatialPeriod {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ))
    (a : ℝ) (ha : 0 < a) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (j : Fin (d + 1)) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    extendedPhysicalBackground d a ha
        (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z (y + spatialFiberEquiv L (OAI.Analysis.PDE.Dirichlet.coordinateVector (j, 0)))) =
      extendedPhysicalBackground d a ha (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) := by
  have hp : OAI.Analysis.PDE.Green.physicalSpatialProjection d (y + spatialFiberEquiv L (OAI.Analysis.PDE.Dirichlet.coordinateVector (j, 0))) =
      OAI.Analysis.PDE.Green.physicalSpatialProjection d y := by
    ext i
    simp [OAI.Analysis.PDE.Green.physicalSpatialProjection_apply, spatialFiberEquiv_apply, spatialFiberChange,
      OAI.Analysis.PDE.Dirichlet.coordinateVector]
  simp only [extendedPhysicalBackground, awayZeroExtension, physicalNullHeight,
    physicalBackground, physicalToNullCurrentPoint_imaginary, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber, hp]

theorem scaled_outer_exists {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (v : Fin n → Quaternion ℝ) :
    ∃ w : Fin n → Quaternion ℝ, c • OAI.Analysis.Calculus.Quaternion.outer v = OAI.Analysis.Calculus.Quaternion.outer w := by
  refine ⟨Real.sqrt c • v, ?_⟩
  apply Matrix.ext
  intro i j
  simp only [OAI.Analysis.Calculus.Quaternion.outer, Matrix.smul_apply, Pi.smul_apply, Quaternion.star_smul,
    smul_mul_assoc, mul_smul_comm, smul_smul, ← sq, Real.sq_sqrt hc]

theorem extendedPhysicalBackground_fiber_rank_one {d : ℕ}
    (a : ℝ) (ha : 0 < a) (lam : ℝ) (hlam : 0 ≤ lam) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (ht : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3)
    (hr : spatialDefiningFunction d a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0) :
    ∃ w : Fin (d + 1) → Quaternion ℝ,
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun y => lam * extendedPhysicalBackground d a ha
        (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y)) y = OAI.Analysis.Calculus.Quaternion.outer w := by
  have ht' : a ≤ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y)).1‖ := by
    simpa only [OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber] using ht
  have hr' : OAI.Analysis.PDE.Green.physicalFullDefining d a (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) ≤ 0 := by
    simpa only [OAI.Analysis.PDE.Green.physicalFullDefining, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber, spatialDefiningFunction,
      Function.comp_apply] using hr
  have hy : physicalNullHeight d (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) ≠ 0 := norm_pos_iff.mp
    (ha.trans_le (physicalNullHeight_on_closed_fiber d a ha _ ht' hr'))
  rw [OAI.Analysis.PDE.Green.quaternionHessian_fiberEmbedding OAI.Analysis.Calculus.Quaternion.threeSlots
    ((contDiff_const.mul (contDiff_extendedPhysicalBackground d a ha)).of_le (by simp)),
    extendedPhysicalBackground_scaled_hessian a ha lam _ ht' hr',
    physicalBackground_hessian_rank_one d _ hy, smul_smul]
  exact scaled_outer_exists (mul_nonneg hlam (by norm_num)) _

theorem extendedPhysical_background_energy_eq {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (lam : ℝ)
    (u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (ht : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) :
    OAI.Analysis.PDE.Green.setFiberCombinedEnergy OAI.Analysis.Calculus.Quaternion.threeSlots lam (physicalLatticeEnergyCell R a)
      (physicalLatticeCurrent R h a κ cR cI v)
      (fun x => lam * extendedPhysicalBackground d a ha x) u z =
    OAI.Analysis.PDE.Green.setFiberCombinedEnergy OAI.Analysis.Calculus.Quaternion.threeSlots lam (physicalLatticeEnergyCell R a)
      (physicalLatticeCurrent R h a κ cR cI v)
      (fun x => lam * physicalBackground d x) u z := by
  apply setIntegral_congr_fun (by
    rw [physicalLatticeEnergyCell_fiber, physicalPacketSplit_latticeCell]
    exact ((isCompact_closedPhysicalSpatialCell R).measurableSet.prod
      (OAI.Analysis.PDE.Green.isOpen_physical_fiber a (OAI.Analysis.PDE.Green.energyComplexTime z) ha ht).measurableSet).preimage
        (physicalPacketSplit d).measurable)
  intro y hy
  have hg := (extendedPhysical_fields_eq_near_fiber R h a ha κ cR cI v z ht hy).2
  apply combinedEnergyDensity_congr_germ OAI.Analysis.Calculus.Quaternion.threeSlots lam rfl _ Filter.EventuallyEq.rfl
  filter_upwards [hg] with x hx
  rw [hx]

/-- Positivity and two-sided comparison for the literal packet energy and
the literal rational background. No rank-one or energy-positivity hypothesis
is needed: both are consequences of the displayed formulas and equation. -/
theorem actual_packet_energy_comparison {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (lam : ℝ) (hlam : 0 < lam) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (ht : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) (ht' : ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ≤ 4)
    {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) 3 → ℝ} (hu : ContDiff ℝ 3 u)
    (huperiod : ∀ j y, u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z
      (y + spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) (OAI.Analysis.PDE.Dirichlet.coordinateVector (j, 0)))) =
        u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y))
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
  let B := fun x => lam * extendedPhysicalBackground (n + 1) a ha x
  have hB : ContDiff ℝ 3 B :=
    (contDiff_const.mul (contDiff_extendedPhysicalBackground (n + 1) a ha)).of_le (by simp)
  have hmem (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3)
      (hy : y ∈ (spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
        OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z))) :
      y ∈ (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z) ⁻¹' physicalLatticeEnergyCell R a := by
    rwa [physicalLatticeEnergyCell_fiber]
  have hH (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3)
      (hy : y ∈ (spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
        OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z))) :
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => B (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) + u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)) y =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun y =>
        lam * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) y +
          u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)) y := by
    apply OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ
    have hg := (extendedPhysical_fields_eq_near_fiber R h a ha κ cR cI v z ht (hmem y hy)).2
    have hc : Continuous (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3 => OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) := by
      unfold OAI.Analysis.PDE.Green.fiberEmbedding
      fun_prop
    filter_upwards [hg.comp_tendsto hc.continuousAt] with w hw
    change extendedPhysicalBackground (n + 1) a ha (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z w) =
      physicalBackground (n + 1) (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z w) at hw
    dsimp only [B]
    rw [hw, physicalBackground_fiber]
  have hb := packet_combined_energy_comparison R h a hh ha κ cR cI v OAI.Analysis.Calculus.Quaternion.threeSlots lam hlam z ht ht'
    hB hu (fun j y => congrArg (fun q : ℝ => lam * q)
      (extendedPhysicalBackground_spatialPeriod _ a ha z j y)) huperiod huz hu0
    (fun y hy => by rw [hH y hy]; exact hpos y hy)
    (fun y hy => extendedPhysicalBackground_fiber_rank_one a ha lam hlam.le z ht y (by
      have hr := (physicalLatticeEnergyCell_fiber_defining_neg R a z (hmem y hy)).le
      simpa only [OAI.Analysis.PDE.Green.physicalFullDefining, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber, spatialDefiningFunction,
        Function.comp_apply] using hr))
    (fun y hy => by rw [hH y hy]; exact heq y hy)
  dsimp only at hb ⊢
  dsimp only [B] at hb
  rw [extendedPhysical_background_energy_eq R h a ha κ cR cI v lam u z ht] at hb
  exact hb

end OAI.Analysis.PDE.Concentration
