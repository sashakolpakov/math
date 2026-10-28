import OAI.Analysis.PDE.Concentration.Physical.Comparison
import OAI.Analysis.PDE.Concentration.Input.Exponent
import OAI.Analysis.PDE.Concentration.Packet.Fiber

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Module OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped ContDiff

/-- The source's input bound for the actual Dirichlet solution and actual
regularized packet current. All constants precede the frequency scale,
packet coefficients, rotated lattice and solution. Only the genuine PDE and
boundary data remain as solution hypotheses. -/
theorem packet_input_solution_bound {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
      (h L : ℝ), 0 < h → h ≤ 1 → 1 ≤ L → ∀ {ι : Type} [Fintype ι]
      (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ), (∀ k, 0 < κ k) →
      (∀ k i, ∃ m : ℤ, inner ℝ (packetSpatialFrequency (κ k) (v k)) (R (EuclideanSpace.single i 1)) =
        (m : ℝ) * (2 * Real.pi) / 100) →
      (∀ k, h • packetSpatialFrequency (κ k) (v k) ∈ K) →
      (∀ k, Real.sqrt L * ‖gaussianVelocity (h • packetSpatialFrequency (κ k) (v k))‖ ≤ A) →
      (∀ y, ‖packetBaseWave κ cR cI v 0 y‖ ≤ 1) →
      ∀ (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3), z (0, 0) = 0 →
      h * L ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ → ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ≤ 4 * (h * L) →
      ∀ (basis : Basis (Fin (n + 2)) ℝ (Fin (n + 2) → ℝ))
        (u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3 → ℝ) (lam : ℝ), 0 ≤ lam →
      ContDiffOn ℝ 2 u {y | spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0} →
      ContinuousOn u {y | spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0} →
      OAI.Analysis.PDE.Dirichlet.LatticePeriodic (physicalSpatialSplit (n + 1)) basis u →
      (∀ y, spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) y = 0 → u y = 0) →
      (∀ y, spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 →
        OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
          (fun w => lam * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w + u w) y) =
        lam * (physicalLatticeCurrent R h (h * L) κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re) →
      ∀ y, spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0 →
        -u y ≤ C * L ^ (1 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1)) := by
  obtain ⟨Cs, hCs, hsup⟩ := packet_sector_input_sup hK hpos A hA
  obtain ⟨c, hc, hsolution⟩ := physical_input_solution_bound n
  obtain ⟨C, hC, hcoef⟩ := exists_input_barrier_coefficient (n + 1) (by omega) hCs hc
  refine ⟨C, hC, ?_⟩
  intro R h L hh hh1 hL ι _ κ cR cI v hκ hm hfreq hsector hnorm z hz ht ht'
    basis u lam hlam hu huc huper hubd hPDE y hy
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let b : ℝ := C * L ^ (1 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1))
  have hb : 0 < b := mul_pos hC (Real.rpow_pos_of_pos hL0 _)
  have hdensity (w : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3)
      (hw : spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) w < 0) :
      (physicalLatticeCurrent R h (h * L) κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z w) 0 0).re ≤
        (b * (c / (h * L) ^ 2)) ^ (n + 1) := by
    rw [physicalLatticeCurrent_input_density R h (h * L) κ cR cI v z hz]
    have hs' := hsup R h L hh hL κ cR cI v hκ hm hfreq hsector 0 1 hnorm
      (OAI.Analysis.PDE.Green.energyComplexTime z) ht ht' (OAI.Analysis.PDE.Green.physicalSpatialProjection (n + 1) w) hw.le
      (physicalSpatialRealVector (n + 1) w)
    simp only [one_pow, mul_one] at hs'
    exact hs'.trans (by simpa only [b, Nat.cast_add, Nat.cast_one] using hcoef h L hh hh1 hL)
  exact (hsolution (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) (mul_pos hh hL0) ht ht'
    basis u (fun w => (physicalLatticeCurrent R h (h * L) κ cR cI v
      (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z w) 0 0).re) b lam hb hlam hu huc huper hubd hPDE hdensity y hy).2

end OAI.Analysis.PDE.Concentration
