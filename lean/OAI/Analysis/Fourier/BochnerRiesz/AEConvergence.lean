import OAI.Analysis.Fourier.BochnerRiesz.CompactExtension

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz


def inverseRadiusAt (R : ℝ) : InverseRadius :=
  ⟨min 1 (max 0 R⁻¹), le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

theorem inverseRadiusAt_eq {R : ℝ} (hR : 1 ≤ R) :
    (inverseRadiusAt R : ℝ) = R⁻¹ := by
  have hr : 0 < R := by linarith
  change min 1 (max 0 R⁻¹) = R⁻¹
  rw [max_eq_right (inv_nonneg.mpr hr.le), min_eq_right]
  simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hR)

theorem tendsto_inverseRadiusAt :
    Tendsto inverseRadiusAt atTop (𝓝 inverseRadiusZero) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun R : ℝ => min 1 (max 0 R⁻¹)) atTop (𝓝 0)
  have H := (tendsto_const_nhds (x := (1 : ℝ))).min
    ((tendsto_const_nhds (x := (0 : ℝ))).max tendsto_inv_atTop_zero)
  simpa using H

def brFamilyRepresentative {n : ℕ} {p : ℝ≥0∞}
    (F : BrFamilyLp n p) (R : ℝ) (x : Space n) : ℂ := F x (inverseRadiusAt R)

theorem tendsto_brFamilyRepresentative {n : ℕ} {p : ℝ≥0∞}
    (F : BrFamilyLp n p) (x : Space n) :
    Tendsto (fun R => brFamilyRepresentative F R x) atTop (𝓝 (F x inverseRadiusZero)) :=
  (F x).continuous.continuousAt.tendsto.comp tendsto_inverseRadiusAt

theorem brFamilyRepresentative_schwartz {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {δ : ℝ} (hδ : 0 ≤ δ) (U : BrLp n p →L[ℂ] BrFamilyLp n p)
    (hU : ∀ f : SchwartzMap (Space n) ℂ,
      (U (f.toLp p volume) : Space n → C(InverseRadius, ℂ)) =ᵐ[volume] brCompactFamily hδ f)
    (f : SchwartzMap (Space n) ℂ) :
    ∀ᵐ x ∂volume, ∀ R : ℝ, 1 ≤ R →
      brFamilyRepresentative (U (f.toLp p volume)) R x = OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x := by
  filter_upwards [hU f] with x hx
  intro R hR
  unfold brFamilyRepresentative
  rw [hx]
  have hr : 0 < R := by linarith
  have ht : 0 < (inverseRadiusAt R : ℝ) := by rw [inverseRadiusAt_eq hR]; positivity
  rw [brCompactFamily_pos hδ f x (inverseRadiusAt R) ht, inverseRadiusAt_eq hR, inv_inv]

theorem ae_tendsto_brFamilyRepresentative {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : BrLp n p →L[ℂ] BrFamilyLp n p)
    (hU : ∀ f : BrLp n p, brFamilyEval inverseRadiusZero (U f) = f)
    (f : BrLp n p) :
    ∀ᵐ x ∂volume, Tendsto (fun R => brFamilyRepresentative (U f) R x) atTop (𝓝 (f x)) := by
  have he := brFamilyEval_coe inverseRadiusZero (U f)
  rw [hU f] at he
  filter_upwards [he] with x hx
  rw [hx]
  exact tendsto_brFamilyRepresentative (U f) x

/-- Almost-everywhere Bochner--Riesz summability for every `Lᵖ` input in the
maximal range, with a coherent representative for all large radii at once. -/
theorem localSmoothing_bochnerRiesz_Lp_ae_convergence (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p δ : ℝ} (hp : 2 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] (hδ : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ U : BrLp n (ENNReal.ofReal p) →L[ℂ] BrFamilyLp n (ENNReal.ofReal p),
      ‖U‖ ≤ C ∧
      (∀ f : SchwartzMap (Space n) ℂ, ∀ᵐ x ∂volume, ∀ R : ℝ, 1 ≤ R →
        brFamilyRepresentative (U (f.toLp (ENNReal.ofReal p) volume)) R x = OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x) ∧
      (∀ f : BrLp n (ENNReal.ofReal p), ∀ᵐ x ∂volume,
        Tendsto (fun R => brFamilyRepresentative (U f) R x) atTop (𝓝 (f x))) := by
  obtain ⟨C, hC, U, hUnorm, hUs, hUzero⟩ := localSmoothing_brFamilyLp_operator hls hn hp hδ
  exact ⟨C, hC, U, hUnorm,
    brFamilyRepresentative_schwartz ((le_max_left _ _).trans hδ.le) U hUs,
    ae_tendsto_brFamilyRepresentative U hUzero⟩

end OAI.Analysis.Fourier.BochnerRiesz
