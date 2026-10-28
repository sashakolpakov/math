import OAI.Analysis.Fourier.WavePackets.PhysicalFixedGeometry
import OAI.Analysis.PDE.Concentration.Packet.Solution

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise

local instance {ι : Type*} [Fintype ι] : NormedAddCommGroup (Matrix ι ι (Quaternion ℝ)) :=
  inferInstanceAs (NormedAddCommGroup (ι → ι → Quaternion ℝ))
local instance {ι : Type*} [Fintype ι] : NormedSpace ℝ (Matrix ι ι (Quaternion ℝ)) :=
  inferInstanceAs (NormedSpace ℝ (ι → ι → Quaternion ℝ))

/-- The concrete regularized packet density and rational background supply
every fixed-fiber datum of the general periodic quaternionic theorem. -/
theorem exists_packet_fixed_data_exact {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n + 1) j) 1)) = (l : ℝ) * (2 * Real.pi) / 100)
    (lam : ℝ) (hlam : 0 < lam) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (ht : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) (ht' : ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ≤ 4) :
    ∃ D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.threeSlots
        (OAI.Analysis.PDE.Concentration.physicalSpatialSplit (n + 1)) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R),
      (∀ y, D.defining y < 0 ↔ OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0) ∧
      (∀ y, D.defining y ≤ 0 ↔ OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0) ∧
      (∀ y, OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0 →
        D.defining =ᶠ[𝓝 y] OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) ∧
        D.background =ᶠ[𝓝 y] (fun w => lam * OAI.Analysis.PDE.Concentration.spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w) ∧
        D.density y = lam * (OAI.Analysis.PDE.Concentration.physicalLatticeCurrent R h a κ cR cI v
          (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re) ∧
      D.background = (fun y => lam * OAI.Analysis.PDE.Concentration.extendedPhysicalBackground (n + 1) a ha
        (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y)) ∧
      D.density = (fun y => lam * (OAI.Analysis.PDE.Concentration.extendedPhysicalLatticeCurrent R h a ha κ cR cI v
        (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re) := by
  let emb := fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3 => OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y
  have hemb : ContDiff ℝ ∞ emb :=
    (OAI.Analysis.PDE.Green.contDiff_fiberEmbedding (n + 2) 3 ∞).comp (contDiff_const.prodMk contDiff_id)
  let B := fun y => lam * OAI.Analysis.PDE.Concentration.extendedPhysicalBackground (n + 1) a ha (emb y)
  let F := fun y => lam * (OAI.Analysis.PDE.Concentration.extendedPhysicalLatticeCurrent R h a ha κ cR cI v (emb y) 0 0).re
  have hB : ContDiff ℝ ∞ B :=
    contDiff_const.mul ((OAI.Analysis.PDE.Concentration.contDiff_extendedPhysicalBackground (n + 1) a ha).comp hemb)
  have hF : ContDiff ℝ ∞ F := by
    have hA : ContDiff ℝ ∞ (fun y =>
        (OAI.Analysis.PDE.Concentration.extendedPhysicalLatticeCurrent R h a ha κ cR cI v (emb y) :
          Fin (n + 3) → Fin (n + 3) → Quaternion ℝ)) :=
      (OAI.Analysis.PDE.Concentration.contDiff_extendedPhysicalLatticeCurrent R h a hh ha κ cR cI v).comp hemb
    exact contDiff_const.mul ((OAI.Analysis.PDE.Green.contDiff_quaternion_real ∞).comp
      ((contDiff_apply_apply ℝ (Quaternion ℝ) 0 0).comp hA))
  have hBp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic (OAI.Analysis.PDE.Concentration.physicalSpatialSplit (n + 1)) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R) B := by
    apply OAI.Analysis.PDE.Concentration.latticePeriodic_fiber_of_cell_period (OAI.Analysis.PDE.Concentration.packetFullCoordinates n) R
      (u := fun x => lam * OAI.Analysis.PDE.Concentration.extendedPhysicalBackground (n + 1) a ha x) (z := z)
    intro j x
    rw [OAI.Analysis.PDE.Concentration.extendedPhysicalBackground_cellPeriod (OAI.Analysis.PDE.Concentration.packetFullCoordinates n) R a ha j x]
  have hFp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic (OAI.Analysis.PDE.Concentration.physicalSpatialSplit (n + 1)) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R) F := by
    apply OAI.Analysis.PDE.Concentration.latticePeriodic_fiber_of_cell_period (OAI.Analysis.PDE.Concentration.packetFullCoordinates n) R
      (u := fun x => lam * (OAI.Analysis.PDE.Concentration.extendedPhysicalLatticeCurrent R h a ha κ cR cI v x 0 0).re) (z := z)
    intro j x
    rw [OAI.Analysis.PDE.Concentration.extendedPhysicalLatticeCurrent_cellPeriod (OAI.Analysis.PDE.Concentration.packetFullCoordinates n) R h a ha κ cR cI v j
      (fun i => hfreq i j) x]
  have hfields (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3)
      (hy : OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0) :
      B =ᶠ[𝓝 y] (fun w => lam * OAI.Analysis.PDE.Concentration.spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w) ∧
      F y = lam * (OAI.Analysis.PDE.Concentration.physicalLatticeCurrent R h a κ cR cI v (emb y) 0 0).re := by
    have htime : a ≤ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) (emb y)).1‖ := by
      simpa only [emb, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber] using ht
    have hdom : OAI.Analysis.PDE.Green.physicalFullDefining (n + 1) a (emb y) ≤ 0 := by
      simpa only [emb, OAI.Analysis.PDE.Green.physicalFullDefining, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber,
        OAI.Analysis.PDE.Concentration.spatialDefiningFunction, Function.comp_apply] using hy
    obtain ⟨hA, hBg⟩ := OAI.Analysis.PDE.Concentration.extendedPhysical_fields_eq_near R h a ha κ cR cI v (emb y) htime hdom
    constructor
    · have hg := hBg.comp_tendsto hemb.continuous.continuousAt
      filter_upwards [hg] with w hw
      dsimp only [Function.comp_apply] at hw
      dsimp only [B]
      rw [hw]
      exact congrArg (fun q : ℝ => lam * q) (OAI.Analysis.PDE.Concentration.physicalBackground_fiber (n + 1) z w)
    · exact congrArg (fun A : Matrix (Fin (n + 3)) (Fin (n + 3)) (Quaternion ℝ) => lam * (A 0 0).re)
        hA.eq_of_nhds
  have hFpos (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3)
      (hy : OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0) : 0 < F y := by
    rw [(hfields y hy).2]
    apply mul_pos hlam
    apply OAI.Analysis.PDE.Concentration.physicalLatticeCurrent_time_pos R h a hh ha.ne' κ cR cI v
    · rw [OAI.Analysis.PDE.Concentration.physicalToNullCurrentPoint_fiber_imaginary]
      exact (OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a (OAI.Analysis.PDE.Green.energyComplexTime z) ha ht
        (hy.trans (show (0 : ℝ) ≤ 1 by norm_num))).1
    · rw [OAI.Analysis.PDE.Concentration.physicalToNullCurrentPoint_fiber_imaginary]
      exact hy
  obtain ⟨r, hr, hrp, hrg, hrn, hrl, hrr, hrpos⟩ :=
    exists_physical_dirichlet_geometry a (OAI.Analysis.PDE.Green.energyComplexTime z) ha ht ht' (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)
  let D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.threeSlots (OAI.Analysis.PDE.Concentration.physicalSpatialSplit (n + 1)) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R) := {
    dimension := by omega
    defining := r
    background := B
    density := F
    transverse := {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (OAI.Analysis.PDE.Green.energyComplexTime z) q ≤ 0}
    compact := OAI.Analysis.Calculus.Current.isCompact_physical_fiber_sublevel a (OAI.Analysis.PDE.Green.energyComplexTime z) ha ht 0 (by norm_num)
    bounded := fun x hx => by
      simpa only [OAI.Analysis.PDE.Concentration.physicalSpatialSplit_snd, OAI.Analysis.PDE.Concentration.spatialDefiningFunction, Function.comp_apply,
        Set.mem_ofPred_eq] using (hrl x).mp hx
    defining_smooth := hr
    background_smooth := hB
    density_smooth := hF
    defining_periodic := hrp
    background_periodic := hBp
    density_periodic := hFp
    regular := hrr
    defining_positive := hrpos
    background_nonnegative := fun y hy => by
      obtain ⟨w, hw⟩ := OAI.Analysis.PDE.Concentration.extendedPhysicalBackground_fiber_rank_one a ha lam hlam.le z ht y ((hrl y).mp hy)
      change (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots B y)).PosSemidef
      rw [hw]
      exact OAI.LinearAlgebra.Moore.complexify_outer_posSemidef w
    background_degenerate := fun y hy => by
      obtain ⟨w, hw⟩ := OAI.Analysis.PDE.Concentration.extendedPhysicalBackground_fiber_rank_one a ha lam hlam.le z ht y ((hrl y).mp hy)
      change OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots B y) = 0
      rw [hw]
      exact OAI.LinearAlgebra.Moore.mooreDet_outer_zero n w
    density_positive := fun y hy => hFpos y ((hrl y).mp hy) }
  exact ⟨D, hrn, hrl, (fun y hy => ⟨hrg y hy, hfields y hy⟩), rfl, rfl⟩

/-- The fixed-fiber data, with the physical formulas on the closed fiber. -/
theorem exists_packet_fixed_data {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n + 1) j) 1)) = (l : ℝ) * (2 * Real.pi) / 100)
    (lam : ℝ) (hlam : 0 < lam) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (ht : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) (ht' : ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ≤ 4) :
    ∃ D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.threeSlots
        (OAI.Analysis.PDE.Concentration.physicalSpatialSplit (n + 1)) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R),
      (∀ y, D.defining y < 0 ↔ OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0) ∧
      (∀ y, D.defining y ≤ 0 ↔ OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0) ∧
      (∀ y, OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0 →
        D.defining =ᶠ[𝓝 y] OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) ∧
        D.background =ᶠ[𝓝 y] (fun w => lam * OAI.Analysis.PDE.Concentration.spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w) ∧
        D.density y = lam * (OAI.Analysis.PDE.Concentration.physicalLatticeCurrent R h a κ cR cI v
          (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re) := by
  obtain ⟨D,hn,hl,hg,_,_⟩ := exists_packet_fixed_data_exact R h a hh ha κ cR cI v hfreq lam hlam z ht ht'
  exact ⟨D,hn,hl,hg⟩

end OAI.Analysis.Fourier.WavePackets
