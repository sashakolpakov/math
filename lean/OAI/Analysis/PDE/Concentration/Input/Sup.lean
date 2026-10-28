import OAI.Analysis.PDE.Concentration.Input.Sector

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set OAI.Analysis.Calculus.Current
open scoped ContDiff

/-- Uniform input supremum on the actual physical fiber, with the fixed
cutoffs constructed internally and the cofactor error displayed separately. -/
theorem packet_sector_input_sup {d : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
      (h L : ℝ), 0 < h → 1 ≤ L → ∀ {ι : Type} [Fintype ι]
      (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ), (∀ k, 0 < κ k) →
      (∀ k i, ∃ m : ℤ, inner ℝ (packetSpatialFrequency (κ k) (v k)) (R (EuclideanSpace.single i 1)) =
        (m : ℝ) * (2 * Real.pi) / 100) →
      (∀ k, h • packetSpatialFrequency (κ k) (v k) ∈ K) →
      (∀ k, Real.sqrt L * ‖gaussianVelocity (h • packetSpatialFrequency (κ k) (v k))‖ ≤ A) →
      ∀ (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (B : ℝ), (∀ y, ‖packetBaseWave κ cR cI v x y‖ ≤ B) →
      ∀ (τ : ℂ), h * L ≤ ‖τ‖ → ‖τ‖ ≤ 4 * (h * L) →
      ∀ q : Option (Fin d) → ℂ, OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) (h * L) τ q ≤ 0 →
      ∀ y, OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h (h * L) κ cR cI v
        (x - nullSpatialShift y) (OAI.Analysis.Calculus.Current.physicalEmbedding τ q)) ≤
        C * (((h ^ d)⁻¹ * L ^ (((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 - d / 2)) ^ 2 * B ^ 2 +
          h ^ (50 * (d + 1)) / (h * L) ^ (2 * (d + 1))) := by
  obtain ⟨ρ, χ, hρ, hcρ, hχ, hcχ, hpρ, heρ, heχ⟩ := exists_sector_cutoffs hK hpos A hA
  obtain ⟨Cs, hCs, hb⟩ := packet_density_upper hρ hcρ hχ hcχ hpρ 1
  obtain ⟨Co, hCo, hco⟩ := timeComponent_fiberCofactor_bound d
  let σ : ℝ := ((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 - d / 2
  have hσ : 0 ≤ σ := by
    dsimp [σ, gaussianDerivativeOrder]
    push_cast
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  let P : ℝ := (12 : ℝ) ^ σ
  have hP : 0 ≤ P := Real.rpow_nonneg (by norm_num) _
  refine ⟨Cs * P ^ 2 + Co, by positivity, ?_⟩
  intro R h L hh hL ι _ κ cR cI v hκ hm hfreq hsector x B hB τ ht ht' q hr y
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have ha : 0 < h * L := mul_pos hh hL0
  obtain ⟨hyl, hyu⟩ := physical_input_height (h * L) τ q ha ht ht' hr
  let ℓ := ‖OAI.Analysis.Calculus.Current.physicalEmbedding τ q none‖ / h
  have hl : L ≤ ℓ := (le_div_iff₀ hh).mpr (by nlinarith)
  have hu : ℓ ≤ 12 * L := (div_le_iff₀ hh).mpr (by nlinarith)
  have he : ‖OAI.Analysis.Calculus.Current.physicalEmbedding τ q none‖ = h * ℓ := by dsimp [ℓ]; field_simp
  have hcut (k : ι) : radialAngularCutoff ρ χ (Real.sqrt ℓ)
      (h • packetSpatialFrequency (κ k) (v k)) = 1 :=
    scaled_sector_cutoff_eq_one hA hL0 (hL0.le.trans hl) hu heχ (heρ _ (hfreq k)) (hsector k)
  have hraw := hb R h ℓ (h * L) hh (hL.trans hl) κ cR cI v hκ x (OAI.Analysis.Calculus.Current.physicalEmbedding τ q)
    he (transverseRatio_norm_le_one (h * L) _ hr) hcut hm B hB y
  have hp : ℓ ^ σ ≤ P * L ^ σ := by
    calc
      _ ≤ (12 * L) ^ σ := Real.rpow_le_rpow (hL0.le.trans hl) hu hσ
      _ = _ := Real.mul_rpow (by norm_num) hL0.le
  have hq : ((h ^ d)⁻¹ * ℓ ^ σ) ^ 2 ≤
      P ^ 2 * ((h ^ d)⁻¹ * L ^ σ) ^ 2 := by
    have h := pow_le_pow_left₀ (show 0 ≤ (h ^ d)⁻¹ * ℓ ^ σ by positivity)
      (mul_le_mul_of_nonneg_left hp (show 0 ≤ (h ^ d)⁻¹ by positivity)) 2
    convert h using 1 ; ring
  have hreg := hco (h * L) (OAI.Analysis.Calculus.Current.physicalEmbedding τ q) ha hyl hr
  have hmain := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hCs) (sq_nonneg B)
  have herr := mul_le_mul_of_nonneg_left hreg (pow_nonneg hh.le (50 * (d + 1)))
  change OAI.Analysis.Calculus.Current.timeComponent _ ≤ (Cs * P ^ 2 + Co) *
    (((h ^ d)⁻¹ * L ^ σ) ^ 2 * B ^ 2 + h ^ (50 * (d + 1)) / (h * L) ^ (2 * (d + 1)))
  apply hraw.trans
  have hm0 : 0 ≤ ((h ^ d)⁻¹ * L ^ σ) ^ 2 * B ^ 2 := by positivity
  have he0 : 0 ≤ h ^ (50 * (d + 1)) / (h * L) ^ (2 * (d + 1)) := by positivity
  calc
    _ ≤ Cs * P ^ 2 * (((h ^ d)⁻¹ * L ^ σ) ^ 2 * B ^ 2) +
        Co * (h ^ (50 * (d + 1)) / (h * L) ^ (2 * (d + 1))) := by
      convert add_le_add hmain herr using 1 ; ring
    _ ≤ _ := by
      nlinarith [mul_nonneg hCo.le hm0, mul_nonneg (mul_nonneg hCs (sq_nonneg P)) he0]

end OAI.Analysis.PDE.Concentration
