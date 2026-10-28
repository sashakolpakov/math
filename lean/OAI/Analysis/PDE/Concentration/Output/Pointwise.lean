import OAI.Analysis.PDE.Concentration.Output.Recovery
import OAI.Analysis.PDE.Concentration.Physical.BallEnergy
import OAI.Analysis.PDE.Concentration.LargeBackground

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Metric OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

/-- Recovery followed by the nonlinear quadratic barrier gives the genuine
pointwise output energy. All constants and scale thresholds are chosen
before the packet or the Dirichlet solution. -/
theorem packet_output_pointwise_gain {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η)
    (hv : ∀ η ∈ K, ‖gaussianVelocity η‖ < 1) (A N F B : ℝ)
    (hA : 0 ≤ A) (hN : 0 ≤ N) (hF : 0 ≤ F) (hB : 0 ≤ B) :
    ∃ c C h₀ L₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ 10000 ≤ L₀ ∧
      ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
      (h L : ℝ), 0 < h → h ≤ h₀ → L₀ ≤ L →
      ∀ {ι : Type} [Fintype ι] (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ),
      (∀ k, 0 < κ k) →
      (∀ k i, ∃ m : ℤ, inner ℝ (packetSpatialFrequency (κ k) (v k))
        (R (EuclideanSpace.single i 1)) = (m : ℝ) * (2 * Real.pi) / 100) →
      (∀ k, h • packetSpatialFrequency (κ k) (v k) ∈ K) →
      (∀ k, Real.sqrt L * ‖gaussianVelocity (h • packetSpatialFrequency (κ k) (v k))‖ ≤ A) →
      (Fintype.card ι : ℝ) ≤ N / h ^ (n + 2) →
      (∀ k, κ k ≤ F / h) → (∀ k, ‖(⟨cR k, cI k⟩ : ℂ)‖ ≤ B) →
      (∀ k, (∑ i, |v k i| ^ 2) ≤ 1 / 1600) →
      ∀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3, h * L ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ →
      ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ≤ 4 * (h * L) →
      ∀ u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3 → ℝ,
      ContDiffOn ℝ 2 u {x | spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0} →
      ContinuousOn u {x | spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0} →
      (∀ x, spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0 → u x ≤ 0) →
      (∀ x, spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0 →
        (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun w =>
          largeBackground (n + 1) h * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w + u w) x)).PosSemidef) →
      (∀ x, spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0 →
        OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun w =>
          largeBackground (n + 1) h * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w + u w) x) =
        largeBackground (n + 1) h *
          (physicalLatticeCurrent R h (h * L) κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z x) 0 0).re) →
      ∀ (y : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)) (q : Option (Fin (n + 1)) → ℂ),
      q ∈ physicalOutputPatch (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) (Real.sqrt L)⁻¹ →
      c * h ^ 2 * (‖packetBaseWave κ cR cI v (physicalNullTime (n + 1) (z (0, 0))) y‖ ^ 2 /
        (C * h ^ (2 * (n + 1)) * L ^ ((gaussianDerivativeOrder (n + 1) : ℝ) + (n + 1)))) ^
          (((n : ℝ) + 2) / ((n : ℝ) + 1)) ≤
        (-u (spatialPacketEmbedding (n + 1) y q)) *
          (physicalLatticeCurrent R h (h * L) κ cR cI v
            (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z (spatialPacketEmbedding (n + 1) y q)) 0 0).re := by
  obtain ⟨C, L₀, hC, hL₀, hrec⟩ := packet_output_full_ball hK hpos hv A hA
  obtain ⟨h₀, hh₀, hh₀1, hupper⟩ := physical_density_le_largeBackground n N F B hN hF hB
  obtain ⟨c, hc, hbar⟩ := exists_physical_ball_energy_lower n
  refine ⟨c, C, h₀, L₀, hc, hC, hh₀, hh₀1, hL₀, ?_⟩
  intro R h L hh hhsmall hL ι _ κ cR cI v hκ hm hf hs hcount hfreq hcoeff hvel
    z ht ht' u hu huc hu0 hPSD hPDE y q hq
  have hL0 : 0 < L := by linarith
  have hha : h ≤ h * L := by nlinarith
  let x₀ := spatialPacketEmbedding (n + 1) y q
  let den : ℝ := C * h ^ (2 * (n + 1)) * L ^ ((gaussianDerivativeOrder (n + 1) : ℝ) + (n + 1))
  let m : ℝ := ‖packetBaseWave κ cR cI v (physicalNullTime (n + 1) (z (0, 0))) y‖ ^ 2 / den
  have hden : 0 < den := by dsimp [den]; positivity
  have hm0 : 0 ≤ m := div_nonneg (sq_nonneg _) hden.le
  obtain ⟨hball, hlower⟩ := hrec R h L hh hL κ cR cI v hκ hm hf hs z ht ht' y q hq
  have hmlower (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3) (hx : x ∈ closedBall x₀ h) :
      m ≤ (physicalLatticeCurrent R h (h * L) κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z x) 0 0).re := by
    apply (div_le_iff₀ hden).mpr
    simpa only [den, mul_comm, Nat.cast_add, Nat.cast_one, Nat.add_assoc] using hlower x hx
  have hx₀ : x₀ ∈ closedBall x₀ h := mem_closedBall_self hh.le
  have hml : m ≤ largeBackground (n + 1) h ^ (n + 1) :=
    (hmlower x₀ hx₀).trans (hupper R h (h * L) κ cR cI v z x₀ hh hhsmall hha ht
      hκ hcount hfreq hcoeff hvel (hball hx₀).le)
  exact hbar R h (h * L) hh (mul_pos hh hL0) κ cR cI v z ht x₀
    (largeBackground (n + 1) h) m (largeBackground_pos (n + 1) hh) hm0 hml hball u
    (hu.mono (fun x hx => hball (ball_subset_closedBall hx)))
    (huc.mono (fun x hx => show spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0 from
      (show spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0 from hball hx).le))
    (fun x hx => hu0 x (hball hx).le)
    (fun x hx => hPSD x (hball (ball_subset_closedBall hx)))
    (fun x hx => hPDE x (hball (ball_subset_closedBall hx)))
    (fun x hx => hmlower x (ball_subset_closedBall hx))

end OAI.Analysis.PDE.Concentration
