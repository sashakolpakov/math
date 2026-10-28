import OAI.Analysis.Fourier.WavePackets.Packet.FixedData
import OAI.Analysis.Fourier.WavePackets.Dirichlet.Descent

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped Topology ContDiff ComplexOrder

/-- Fixed-fiber solvability of the literal packet equation from the general
four-slot periodic Dirichlet theorem. All geometric, positivity, lattice,
and dummy-coordinate hypotheses are discharged here. Joint time-parameter
smoothness is the separate implicit-function step. -/
theorem packet_fixed_fiber_of_fourSlot (hsolve : FourSlotDirichletExistence)
    {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n + 1) j) 1)) = (l : ℝ) * (2 * Real.pi) / 100)
    (lam : ℝ) (hlam : 0 < lam) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (ht : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) (ht' : ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ≤ 4) :
    ∃ u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3 → ℝ,
      ContDiff ℝ ∞ u ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic (OAI.Analysis.PDE.Concentration.physicalSpatialSplit (n + 1)) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R) u ∧
      (∀ y, OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y = 0 → u y = 0) ∧
      (∀ y, OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0 → u y ≤ 0) ∧
      (∀ y, OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 →
        (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
          (fun w => lam * OAI.Analysis.PDE.Concentration.spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w + u w) y)).PosDef) ∧
      (∀ y, OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 →
        OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
          (fun w => lam * OAI.Analysis.PDE.Concentration.spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w + u w) y) =
        lam * (OAI.Analysis.PDE.Concentration.physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re) := by
  obtain ⟨D, hn, hl, hg⟩ := exists_packet_fixed_data R h a hh ha κ cR cI v hfreq lam hlam z ht ht'
  obtain ⟨S4⟩ := hsolve (n + 2) ((Fin (n + 2) → ℝ) × (Fin (n + 2) → ℝ))
    (Option (Fin (n + 1)) → ℂ) (Fin (n + 2) ⊕ Fin (n + 2))
    (paddedLatticeSplit (OAI.Analysis.PDE.Concentration.physicalSpatialSplit (n + 1)))
    (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)) D.padFourth
  let S := S4.descend D
  have hH (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3)
      (hy : OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0) :
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun w => D.background w + S.u w) y =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun w => lam * OAI.Analysis.PDE.Concentration.spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w + S.u w) y := by
    apply OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ
    filter_upwards [(hg y hy).2.1] with w hw
    rw [hw]
  refine ⟨S.u, S.smooth, S.periodic, ?_, ?_, ?_, ?_⟩
  · intro y hy
    apply S.boundary
    exact (hg y hy.le).1.eq_of_nhds.trans hy
  · intro y hy
    change S4.u (insertFourth (n + 2) y) ≤ 0
    apply S4.nonpositive
    change D.defining (dropFourth (n + 2) (insertFourth (n + 2) y)) ≤ 0
    rw [dropFourth_insertFourth]
    exact (hl y).mpr hy
  · intro y hy
    rw [← hH y hy.le]
    exact S.admissible y ((hn y).mpr hy)
  · intro y hy
    rw [← hH y hy.le, S.equation y ((hn y).mpr hy)]
    exact (hg y hy.le).2.2

end OAI.Analysis.Fourier.WavePackets
