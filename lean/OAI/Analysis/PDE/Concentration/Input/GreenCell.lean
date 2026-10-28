import OAI.Analysis.PDE.Concentration.Packet.Compact
import OAI.Analysis.PDE.Concentration.Input.Normalized

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Module _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped ContDiff

/-- The normalized input estimate on the literal rotated Green cell. The
measure conversion, integrability, scalar barrier, packet bounds, and
regularization-error absorption are all proved internally. -/
theorem packet_input_Green_X0 {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)),
      (∀ j, ‖R (EuclideanSpace.single j 1)‖ ≤ 1) →
      ∀ (h L : ℝ), 0 < h → h ≤ 1 → 1 ≤ L → ∀ {ι : Type} [Fintype ι]
      (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ) (m : ι → Option (Fin (n + 1)) → ℤ),
      Function.Injective m → (∀ k, 0 < κ k) →
      (∀ k i, inner ℝ (packetSpatialFrequency (κ k) (v k)) (R (EuclideanSpace.single i 1)) =
        (m k i : ℝ) * (2 * Real.pi) / 100) →
      (∀ k, h • packetSpatialFrequency (κ k) (v k) ∈ K) →
      (∀ k, Real.sqrt L * ‖gaussianVelocity (h • packetSpatialFrequency (κ k) (v k))‖ ≤ A) →
      (∀ y, ‖packetBaseWave κ cR cI v 0 y‖ ≤ 1) →
      (∀ b < (1 : ℝ), ∃ y, b < ‖packetBaseWave κ cR cI v 0 y‖ ^ 2) →
      ∀ (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3), z (0, 0) = 0 →
      h * L ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ → ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ≤ 4 * (h * L) →
      ∀ (basis : Basis (Fin (n + 2)) ℝ (Fin (n + 2) → ℝ))
        (u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3 → ℝ) (lam : ℝ), 0 ≤ lam →
      ContDiffOn ℝ 2 u {y | spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0} →
      ContinuousOn u {y | spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0} →
      OAI.Analysis.PDE.Dirichlet.LatticePeriodic (physicalSpatialSplit (n + 1)) basis u →
      (∀ y, spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) y = 0 → u y = 0) →
      (∀ y, spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 → u y ≤ 0) →
      (∀ y, spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 →
        OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
          (fun w => lam * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w + u w) y) =
        lam * (physicalLatticeCurrent R h (h * L) κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re) →
      (∫ y in spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
          OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z),
          (-u y) * (physicalLatticeCurrent R h (h * L) κ cR cI v
            (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re) ≤
        C * h ^ 2 * L ^ ((n : ℝ) + 4 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1)) *
          (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v 0 y‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := packet_input_X0_normalized hK hpos A hA
  refine ⟨C, hC, ?_⟩
  intro R hR h L hh hh1 hL ι _ κ cR cI v m hinj hκ hm hfreq hsector hnorm hnorm'
    z hz ht ht' basis u lam hlam hu huc huper hubd hu0 hPDE
  have ha : 0 < h * L := mul_pos hh (lt_of_lt_of_le zero_lt_one hL)
  rw [integral_physicalLatticeFiber R (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z)
    (OAI.Analysis.PDE.Green.isOpen_physical_fiber (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) ha ht).measurableSet
    (integrable_packet_weighted_physicalCell R h (h * L) hh ha κ cR cI v z ht huc)]
  exact hbound R hR h L hh hh1 hL κ cR cI v m hinj hκ hm hfreq hsector hnorm hnorm'
    z hz ht ht' basis u lam hlam hu huc huper hubd hu0 hPDE

end OAI.Analysis.PDE.Concentration
