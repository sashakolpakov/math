import OAI.Analysis.PDE.Concentration.Input.Density
import OAI.Analysis.PDE.Concentration.SectorCutoffs

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set OAI.Analysis.Calculus.Current
open scoped ContDiff

/-- Input-density estimate with the auxiliary cutoffs eliminated. Only the
actual compact frequency localization and shrinking angular sector remain. -/
theorem packet_sector_input_density {d : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
      (h L : ℝ), 0 < h → 1 ≤ L → ∀ {ι : Type} [Fintype ι]
      (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ),
      Function.Injective m → (∀ k, 0 < κ k) →
      (∀ k i, inner ℝ (packetSpatialFrequency (κ k) (v k)) (R (EuclideanSpace.single i 1)) =
        (m k i : ℝ) * (2 * Real.pi) / 100) →
      (∀ k, h • packetSpatialFrequency (κ k) (v k) ∈ K) →
      (∀ k, Real.sqrt L * ‖gaussianVelocity (h • packetSpatialFrequency (κ k) (v k))‖ ≤ A) →
      ∀ (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (τ : ℂ), h * L ≤ ‖τ‖ → ‖τ‖ ≤ 4 * (h * L) →
      (∫ q in {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) (h * L) τ q < 0},
        ∫ y in physicalSpatialCell R,
          OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h (h * L) κ cR cI v
            (x - nullSpatialShift y) (OAI.Analysis.Calculus.Current.physicalEmbedding τ q))) ≤
        C * (h ^ 2 * L ^ (d + 2) * (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v x y‖ ^ 2) +
          volume.real (physicalSpatialCell R) * h ^ (50 * (d + 1))) := by
  obtain ⟨ρ, χ, hρ, hcρ, hχ, hcχ, hpρ, heρ, heχ⟩ := exists_sector_cutoffs hK hpos A hA
  obtain ⟨C, hC, hb⟩ := packet_input_density_integral hρ hcρ hχ hcχ hpρ
  refine ⟨C, hC, ?_⟩
  intro R h L hh hL ι _ κ cR cI v m hinj hκ hm hfreq hsector x τ ht ht'
  apply hb R h L hh hL κ cR cI v m hinj hκ hm _ x τ ht ht'
  intro ℓ hl hu k
  exact scaled_sector_cutoff_eq_one hA (by linarith) (by linarith) hu heχ
    (heρ _ (hfreq k)) (hsector k)

end OAI.Analysis.PDE.Concentration
