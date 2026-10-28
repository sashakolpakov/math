import OAI.Analysis.PDE.Concentration.IntegratedDensity
import OAI.Analysis.PDE.Concentration.FiberVolume
import OAI.Analysis.PDE.Concentration.Input.Geometry
import OAI.Analysis.PDE.Concentration.Input.Scale
import OAI.Analysis.PDE.Green.Physical.Fubini

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Green
open scoped ContDiff

/-- The complete small-time fiber integral of the actual regularized packet
current. The last term is the genuine cofactor regularization error. Here `L`
is the ratio `a / h`; the constants precede all semiclassical and packet data. -/
theorem packet_input_density_integral {d : ℕ} {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
      (h L : ℝ), 0 < h → 1 ≤ L → ∀ {ι : Type} [Fintype ι]
      (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ),
      Function.Injective m → (∀ k, 0 < κ k) →
      (∀ k i, inner ℝ (packetSpatialFrequency (κ k) (v k)) (R (EuclideanSpace.single i 1)) =
        (m k i : ℝ) * (2 * Real.pi) / 100) →
      (∀ ℓ : ℝ, L ≤ ℓ → ℓ ≤ 12 * L → ∀ i,
        radialAngularCutoff ρ χ (Real.sqrt ℓ) (h • packetSpatialFrequency (κ i) (v i)) = 1) →
      ∀ (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (τ : ℂ), h * L ≤ ‖τ‖ → ‖τ‖ ≤ 4 * (h * L) →
      (∫ q in {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) (h * L) τ q < 0},
        ∫ y in physicalSpatialCell R,
          OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h (h * L) κ cR cI v
            (x - nullSpatialShift y) (OAI.Analysis.Calculus.Current.physicalEmbedding τ q))) ≤
        C * (h ^ 2 * L ^ (d + 2) * (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v x y‖ ^ 2) +
          volume.real (physicalSpatialCell R) * h ^ (50 * (d + 1))) := by
  obtain ⟨Cs, hCs, hsp⟩ := packet_spatial_density_upper hρ hcρ hχ hcχ hpos 1
  obtain ⟨Co, hCo, hco⟩ := timeComponent_fiberCofactor_bound d
  obtain ⟨Cv, hCv, hvol⟩ := physical_imaginary_fiber_volume_upper d
  refine ⟨Cv * (Cs + Co), mul_pos hCv (add_pos_of_nonneg_of_pos hCs hCo), ?_⟩
  intro R h L hh hL ι _ κ cR cI v m hinj hκ hm hcut x τ ht ht'
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have ha : 0 < h * L := mul_pos hh hL0
  let S := {q : Option (Fin d) → ℂ | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) (h * L) τ q < 0}
  let E := ∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v x y‖ ^ 2
  let V := volume.real (physicalSpatialCell R)
  let Q := (h ^ d)⁻¹ * L ^ (-(d : ℝ) / 2)
  let B := Cs * Q ^ 2 * E + V * h ^ (50 * (d + 1)) * (Co / (h * L) ^ (2 * (d + 1)))
  have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr (physical_imaginary_fiber_finite (h * L) τ ha ht)
  have hS : MeasurableSet S := (OAI.Analysis.PDE.Green.isOpen_physical_fiber (h * L) τ ha ht).measurableSet
  have hbound (q) (hq : q ∈ S) :
      (∫ y in physicalSpatialCell R,
        OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h (h * L) κ cR cI v
          (x - nullSpatialShift y) (OAI.Analysis.Calculus.Current.physicalEmbedding τ q))) ≤ B := by
    have hr : OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) (h * L) τ q ≤ 0 := hq.le
    obtain ⟨hyl, hyu⟩ := physical_input_height (h * L) τ q ha ht ht' hr
    let ℓ := ‖OAI.Analysis.Calculus.Current.physicalEmbedding τ q none‖ / h
    have hl : L ≤ ℓ := (le_div_iff₀ hh).mpr (by nlinarith)
    have hu : ℓ ≤ 12 * L := (div_le_iff₀ hh).mpr (by nlinarith)
    have he : ‖OAI.Analysis.Calculus.Current.physicalEmbedding τ q none‖ = h * ℓ := by dsimp [ℓ]; field_simp
    have hb := hsp R h ℓ (h * L) hh (hL.trans hl) κ cR cI v m hinj hκ hm x
      (OAI.Analysis.Calculus.Current.physicalEmbedding τ q) he (transverseRatio_norm_le_one (h * L) _ hr) (hcut ℓ hl hu)
    apply hb.trans
    apply add_le_add
    · have hp := Real.rpow_le_rpow_of_nonpos hL0 hl
        (show -(d : ℝ) / 2 ≤ 0 by have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
      have hq' : (h ^ d)⁻¹ * ℓ ^ (-(d : ℝ) / 2) ≤ Q :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq' 2) hCs) hE
    · have hc := hco (h * L) (OAI.Analysis.Calculus.Current.physicalEmbedding τ q) ha hyl hr
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hc
        (show 0 ≤ V * h ^ (50 * (d + 1)) by positivity)
  have hn (q) (hq : q ∈ S) : 0 ≤
      ∫ y in physicalSpatialCell R,
        OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h (h * L) κ cR cI v
          (x - nullSpatialShift y) (OAI.Analysis.Calculus.Current.physicalEmbedding τ q)) := by
    have hr : OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) (h * L) τ q ≤ 0 := hq.le
    have hy := (physical_input_height (h * L) τ q ha ht ht' hr).1
    exact integral_nonneg fun y => (latticeRegularizedCurrent_time_pos R h (h * L) hh ha.ne'
      κ cR cI v _ _ (norm_ne_zero_iff.mp (ha.trans_le hy).ne') hr).le
  have hi : (∫ q in S, ∫ y in physicalSpatialCell R,
        OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h (h * L) κ cR cI v
          (x - nullSpatialShift y) (OAI.Analysis.Calculus.Current.physicalEmbedding τ q))) ≤ volume.real S * B := by
    have he := integral_mono_of_nonneg
      ((ae_restrict_mem hS).mono fun q hq => hn q hq)
      (integrable_const B : Integrable (fun _ : Option (Fin d) → ℂ => B) (volume.restrict S))
      ((ae_restrict_mem hS).mono fun q hq => hbound q hq)
    simpa only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ] using he
  have hv := hvol (h * L) τ ha ht ht'
  calc
    _ ≤ volume.real S * B := hi
    _ ≤ (Cv * (h * L) ^ (2 * (d + 1))) * B := mul_le_mul_of_nonneg_right hv hB
    _ = Cv * Cs * ((h * L) ^ (2 * (d + 1)) * Q ^ 2) * E +
        Cv * Co * (V * h ^ (50 * (d + 1))) := by
      dsimp only [B]
      field_simp
    _ = Cv * Cs * (h ^ 2 * L ^ (d + 2) * E) + Cv * Co * (V * h ^ (50 * (d + 1))) := by
      rw [show (h * L) ^ (2 * (d + 1)) * Q ^ 2 = h ^ 2 * L ^ (d + 2) from input_density_scaling d hh hL0]
      ring
    _ ≤ _ := by
      have hmain : 0 ≤ h ^ 2 * L ^ (d + 2) * E := by positivity
      have herr : 0 ≤ V * h ^ (50 * (d + 1)) := by positivity
      nlinarith [mul_nonneg (mul_nonneg hCv.le hCs) herr,
        mul_nonneg (mul_nonneg hCv.le hCo.le) hmain]

end OAI.Analysis.PDE.Concentration
