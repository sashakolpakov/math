import OAI.Analysis.PDE.Concentration.Input.X0
import OAI.Analysis.PDE.Concentration.Normalization

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Module _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped ContDiff

theorem input_regularization_absorb (d : ℕ) {h L V E C : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hL : 1 ≤ L) (hV : 0 ≤ V) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hlower : V * h ^ (d + 1) ≤ C * E) :
    V * h ^ (50 * (d + 1)) ≤ C * (h ^ 2 * L ^ (d + 2) * E) := by
  have hp := pow_le_pow_of_le_one hh.le hh1 (by omega : (d + 1) + 2 ≤ 50 * (d + 1))
  calc
    _ ≤ V * h ^ ((d + 1) + 2) := mul_le_mul_of_nonneg_left hp hV
    _ = h ^ 2 * (V * h ^ (d + 1)) := by rw [pow_add]; ring
    _ ≤ h ^ 2 * (C * E) := mul_le_mul_of_nonneg_left hlower (sq_nonneg h)
    _ ≤ C * (h ^ 2 * L ^ (d + 2) * E) := by
      have hpow : 1 ≤ L ^ (d + 2) := one_le_pow₀ hL
      have := mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg hC (sq_nonneg h)) hE)
      nlinarith

/-- The fully normalized input `X₀` estimate, including the absorption of the
actual cofactor regularization error. This is the source exponent
`n_physical + 2 + M/(n_physical-1)`; our physical dimension here is `n+2`. -/
theorem packet_input_X0_normalized {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
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
      (∫ q in {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) q < 0},
        ∫ y in physicalSpatialCell R,
          (-u (spatialPacketEmbedding (n + 1) y q)) *
            (physicalLatticeCurrent R h (h * L) κ cR cI v
              (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z (spatialPacketEmbedding (n + 1) y q)) 0 0).re) ≤
        C * h ^ 2 * L ^ ((n : ℝ) + 4 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1)) *
          (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v 0 y‖ ^ 2) := by
  obtain ⟨CX, hCX, hX⟩ := packet_input_X0_bound hK hpos A hA
  obtain ⟨CN, hCN, hN⟩ := compact_angular_energy_lower hK
  refine ⟨CX * (1 + CN), by positivity, ?_⟩
  intro R hR h L hh hh1 hL ι _ κ cR cI v m hinj hκ hm hfreq hsector hnorm hnorm'
    z hz ht ht' basis u lam hlam hu huc huper hubd hu0 hPDE
  have hlower := hN R hR h hh hh1 (fun i => packetSpatialFrequency (κ i) (v i)) m
    (fun i => OAI.Analysis.Calculus.Current.phaseComplex (cR i) (cI i) (OAI.Analysis.Calculus.Current.modeCovector (κ i) (v i)) 0)
    hinj hfreq hm hnorm'
  change volume.real (physicalSpatialCell R) * h ^ (n + 2) ≤
    CN * ∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v 0 y‖ ^ 2 at hlower
  have herr := input_regularization_absorb (n + 1) hh hh1 hL
    (show 0 ≤ volume.real (physicalSpatialCell R) from ENNReal.toReal_nonneg)
    (show 0 ≤ ∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v 0 y‖ ^ 2 from
      integral_nonneg fun y => sq_nonneg _) hCN.le hlower
  have hx := hX R h L hh hh1 hL κ cR cI v m hinj hκ hm hfreq hsector hnorm
    z hz ht ht' basis u lam hlam hu huc huper hubd hu0 hPDE
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let p : ℝ := 1 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1)
  have hpow : L ^ p * L ^ (n + 3) =
      L ^ ((n : ℝ) + 4 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL0]
    congr 1
    dsimp only [p]
    push_cast
    ring
  apply hx.trans
  calc
    _ ≤ CX * L ^ p * ((1 + CN) *
        (h ^ 2 * L ^ (n + 3) * (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v 0 y‖ ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCX.le (Real.rpow_nonneg hL0.le _))
      nlinarith
    _ = CX * (1 + CN) * h ^ 2 * (L ^ p * L ^ (n + 3)) *
        (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v 0 y‖ ^ 2) := by ring
    _ = _ := by rw [hpow]

end OAI.Analysis.PDE.Concentration
