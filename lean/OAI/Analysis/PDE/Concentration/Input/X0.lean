import OAI.Analysis.PDE.Concentration.Input.Solution
import OAI.Analysis.PDE.Concentration.WeightedInput
import OAI.Analysis.PDE.Concentration.Packet.Coordinates

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Module _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped ContDiff

/-- Input bound for the actual weighted density `X₀ = ∫ (-u) μ`. The
regularization term is retained explicitly until the normalized torus
Bernstein lower bound is applied. There is no assumed solution supremum or
weighted-density estimate. -/
theorem packet_input_X0_bound {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
      (h L : ℝ), 0 < h → h ≤ 1 → 1 ≤ L → ∀ {ι : Type} [Fintype ι]
      (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ) (m : ι → Option (Fin (n + 1)) → ℤ),
      Function.Injective m → (∀ k, 0 < κ k) →
      (∀ k i, inner ℝ (packetSpatialFrequency (κ k) (v k)) (R (EuclideanSpace.single i 1)) =
        (m k i : ℝ) * (2 * Real.pi) / 100) →
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
      (∀ y, spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 → u y ≤ 0) →
      (∀ y, spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 →
        OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
          (fun w => lam * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w + u w) y) =
        lam * (physicalLatticeCurrent R h (h * L) κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re) →
      (∫ q in {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) q < 0},
        ∫ y in physicalSpatialCell R,
          (-u (spatialPacketEmbedding (n + 1) y q)) *
            (physicalLatticeCurrent R h (h * L) κ cR cI v
              (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z (spatialPacketEmbedding (n + 1) y q)) 0 0).re) ≤
        C * L ^ (1 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1)) *
          (h ^ 2 * L ^ (n + 3) * (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v 0 y‖ ^ 2) +
            volume.real (physicalSpatialCell R) * h ^ (50 * (n + 2))) := by
  obtain ⟨Cu, hCu, hsol⟩ := packet_input_solution_bound hK hpos A hA
  obtain ⟨Cw, hCw, hweight⟩ := packet_weighted_input_density hK hpos A hA
  refine ⟨Cw * Cu, mul_pos hCw hCu, ?_⟩
  intro R h L hh hh1 hL ι _ κ cR cI v m hinj hκ hm hfreq hsector hnorm z hz ht ht'
    basis u lam hlam hu huc huper hubd hu0 hPDE
  have hb := hsol R h L hh hh1 hL κ cR cI v hκ (fun k i => ⟨m k i, hm k i⟩)
    hfreq hsector hnorm z hz ht ht' basis u lam hlam hu huc huper hubd hPDE
  let B := Cu * L ^ (1 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1))
  have hB : 0 ≤ B := mul_nonneg hCu.le (Real.rpow_nonneg (by linarith) _)
  have hw (q : Option (Fin (n + 1)) → ℂ)
      (hq : OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) q < 0)
      (y : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)) :
      0 ≤ -u (spatialPacketEmbedding (n + 1) y q) ∧ -u (spatialPacketEmbedding (n + 1) y q) ≤ B := by
    have he := spatialPacketEmbedding_defining (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) y q
    have hr : spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z)
        (spatialPacketEmbedding (n + 1) y q) < 0 := he ▸ hq
    exact ⟨neg_nonneg.mpr (hu0 _ hr), hb _ hr.le⟩
  have hfinal := hweight R h L hh hL κ cR cI v m hinj hκ hm hfreq hsector 0
    (OAI.Analysis.PDE.Green.energyComplexTime z) ht ht' (fun q y => -u (spatialPacketEmbedding (n + 1) y q)) B hB hw
  simp_rw [physicalLatticeCurrent_input_density_embedding R h (h * L) κ cR cI v z hz]
  convert hfinal using 1 ; dsimp only [B] ; ring

end OAI.Analysis.PDE.Concentration
