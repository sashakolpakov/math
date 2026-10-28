import OAI.Analysis.PDE.Concentration.Packet.Solution
import OAI.Analysis.PDE.Concentration.Input.GreenCell
import OAI.Analysis.PDE.Concentration.Output.Normalized

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Module Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped ContDiff Topology Matrix.Norms.Elementwise ComplexOrder MatrixOrder

/-- Input control for the actual energy, after the determinant comparison. -/
theorem packet_input_energy_bound {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η) (A : ℝ) (hA : 0 ≤ A) :
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
      ∀ (lam : ℝ), 0 < lam → ∀ S : PhysicalPacketSolution R h (h * L) κ cR cI v lam,
      ∀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3, z ∈ physicalEnergyAnnulus (h * L) → z (0, 0) = 0 →
      ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ≤ 4 * (h * L) →
      packetEnergy R h (h * L) κ cR cI v lam S.u z ≤
        C * h ^ 2 * L ^ ((n : ℝ) + 4 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1)) *
          (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v 0 y‖ ^ 2) := by
  obtain ⟨C, hC, hc⟩ := packet_input_Green_X0 hK hpos A hA
  refine ⟨C, hC, ?_⟩
  intro R hR h L hh hh1 hL ι inst κ cR cI v m hm hκ hfreq hKmem hsector hnorm hnorm'
    lam hlam S z hz hz0 hzt
  have ha : 0 < h * L := mul_pos hh (lt_of_lt_of_le zero_lt_one hL)
  apply (S.energy_comparison hh ha hlam hz).2.2.trans
  exact hc R hR h L hh hh1 hL κ cR cI v m hm hκ hfreq hKmem hsector hnorm hnorm'
    z hz0 hz.1.le hzt (packetSpatialBasis R) (fun y => S.u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y))
    lam hlam.le ((S.fiber_smooth_interior z hz).of_le (by simp))
    (S.fiber_smooth z hz).continuousOn (S.fiber_periodic z)
    (fun y hy => S.fiber_boundary hz hy)
    (fun y hy => S.fiber_nonpositive hz hy.le)
    (fun y hy => S.fiber_equation ha hz hy)

/-- Output control for the actual energy. The dimension-dependent positive
comparison factor is absorbed into the fixed lower-bound constant. -/
theorem packet_output_energy_bound {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η)
    (hcap : ∀ η ∈ K, ‖gaussianVelocity η‖ ≤ 1 / 40) (A : ℝ) (hA : 0 ≤ A) :
    ∃ c h₀ L₀ : ℝ, 0 < c ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ 10000 ≤ L₀ ∧
      ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)),
      (∀ j, ‖R (EuclideanSpace.single j 1)‖ ≤ 1) →
      ∀ (h L : ℝ), 0 < h → h ≤ h₀ → L₀ ≤ L →
      ∀ {ι : Type} [Fintype ι] (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
      (m : ι → Option (Fin (n + 1)) → ℤ), Function.Injective m →
      (∀ k, 0 < κ k) →
      (∀ k i, inner ℝ (packetSpatialFrequency (κ k) (v k))
        (R (EuclideanSpace.single i 1)) = (m k i : ℝ) * (2 * Real.pi) / 100) →
      (∀ k, h • packetSpatialFrequency (κ k) (v k) ∈ K) →
      (∀ k, Real.sqrt L * ‖gaussianVelocity (h • packetSpatialFrequency (κ k) (v k))‖ ≤ A) →
      (∀ y, ‖packetBaseWave κ cR cI v 0 y‖ ≤ 1) →
      ∀ S : PhysicalPacketSolution R h (h * L) κ cR cI v (largeBackground (n + 1) h),
      ∀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3, z ∈ physicalEnergyAnnulus (h * L) →
      ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ≤ 4 * (h * L) →
      c * h ^ 2 * L ^ (1 - (((n : ℝ) + 2) / ((n : ℝ) + 1)) *
        (gaussianDerivativeOrder (n + 1) : ℝ)) *
        (∫ y in physicalSpatialCell R,
          ‖packetBaseWave κ cR cI v (physicalNullTime (n + 1) (z (0, 0))) y‖ ^
            (2 * (((n : ℝ) + 2) / ((n : ℝ) + 1)))) ≤
      packetEnergy R h (h * L) κ cR cI v (largeBackground (n + 1) h) S.u z := by
  obtain ⟨c, h₀, L₀, hc, hh₀, hh₀1, hL₀, hb⟩ := packet_output_X0_normalized hK hpos hcap A hA
  let β : ℝ := ((n : ℝ) + 1) / ((n : ℝ) + 3)
  have hβ : 0 < β := by dsimp [β]; positivity
  refine ⟨β * c, h₀, L₀, mul_pos hβ hc, hh₀, hh₀1, hL₀, ?_⟩
  intro R hR h L hh hsmall hL ι inst κ cR cI v m hm hκ hfreq hKmem hsector hnorm S z hz hzt
  have hLp : 0 < L := by linarith
  have ha : 0 < h * L := mul_pos hh hLp
  have hout := hb R hR h L hh hsmall hL κ cR cI v m hm hκ hfreq hKmem hsector hnorm
    z hz.1.le hzt (fun y => S.u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y))
    ((S.fiber_smooth_interior z hz).of_le (by simp))
    (S.fiber_smooth z hz).continuousOn
    (fun y hy => S.fiber_nonpositive hz hy)
    (fun y hy => (S.fiber_admissible ha hz hy).posSemidef)
    (fun y hy => S.fiber_equation ha hz hy)
  have he := (S.energy_comparison hh ha (largeBackground_pos (n + 1) hh) hz).2.1
  have hhout := (mul_le_mul_of_nonneg_left hout hβ.le).trans he
  simpa only [mul_assoc, β] using hhout

end OAI.Analysis.PDE.Concentration
