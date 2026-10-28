import OAI.Analysis.PDE.Concentration.GaussianFamily
import OAI.Analysis.Calculus.Current.Kernel

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Metric
open scoped ContDiff Topology
open OAI.Analysis.Calculus.Current

abbrev TransverseSpace (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- The dimensionless positive null frequency in the manuscript. -/
def gaussianFrequencyK {d : ℕ} (η : OAI.Analysis.Calculus.Current.SpatialSpace d) : ℝ :=
  (η none + ‖η‖) / Real.sqrt 2

def transverseFrequency {d : ℕ} : OAI.Analysis.Calculus.Current.SpatialSpace d →L[ℝ] TransverseSpace d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj (some i)))

def gaussianVelocity {d : ℕ} (η : OAI.Analysis.Calculus.Current.SpatialSpace d) : TransverseSpace d :=
  (gaussianFrequencyK η)⁻¹ • transverseFrequency η

def gaussianPhaseMap {d : ℕ} (p : TransverseSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d) : TransverseSpace d :=
  Real.sqrt (gaussianFrequencyK p.2 / (2 * Real.pi)) • (p.1 - gaussianVelocity p.2)

theorem continuous_gaussianFrequencyK {d : ℕ} :
    Continuous (gaussianFrequencyK : OAI.Analysis.Calculus.Current.SpatialSpace d → ℝ) := by
  exact ((EuclideanSpace.proj none).continuous.add continuous_norm).div_const _

theorem gaussianFrequencyK_ne_zero_frequency {d : ℕ} {η : OAI.Analysis.Calculus.Current.SpatialSpace d}
    (hη : 0 < gaussianFrequencyK η) : η ≠ 0 := by
  intro h
  subst η
  simp [gaussianFrequencyK] at hη

theorem contDiffAt_gaussianFrequencyK {d : ℕ} {η : OAI.Analysis.Calculus.Current.SpatialSpace d} (hη : η ≠ 0) :
    ContDiffAt ℝ ∞ gaussianFrequencyK η :=
  ((EuclideanSpace.proj none).contDiff.contDiffAt.add (contDiffAt_norm ℝ hη)).div_const _

theorem contDiffOn_gaussianVelocity {d : ℕ} :
    ContDiffOn ℝ ∞ (gaussianVelocity (d := d)) {η | 0 < gaussianFrequencyK η} := by
  intro η hη
  exact (((contDiffAt_gaussianFrequencyK (gaussianFrequencyK_ne_zero_frequency hη)).inv hη.ne').smul
    transverseFrequency.contDiff.contDiffAt).contDiffWithinAt

theorem contDiffOn_gaussianPhaseMap {d : ℕ} :
    ContDiffOn ℝ ∞ (gaussianPhaseMap (d := d))
      {p | 0 < gaussianFrequencyK p.2} := by
  intro p hp
  have hk : ContDiffAt ℝ ∞ (fun q : TransverseSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d =>
      gaussianFrequencyK q.2) p :=
    (contDiffAt_gaussianFrequencyK (gaussianFrequencyK_ne_zero_frequency hp)).comp p contDiffAt_snd
  have hv : ContDiffAt ℝ ∞ (fun q : TransverseSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d =>
      gaussianVelocity q.2) p :=
    (hk.inv hp.ne').smul (transverseFrequency.contDiff.contDiffAt.comp p contDiffAt_snd)
  exact (((hk.div_const _).sqrt (ne_of_gt (div_pos hp (by positivity)))).smul
    (contDiffAt_fst.sub hv)).contDiffWithinAt

theorem gaussianPhaseMap_norm_sq {d : ℕ} (W : TransverseSpace d) (η : OAI.Analysis.Calculus.Current.SpatialSpace d)
    {L : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ gaussianFrequencyK η) :
    Real.pi * ‖Real.sqrt L • gaussianPhaseMap (W, η)‖ ^ 2 =
      L / 2 * gaussianFrequencyK η * ‖W - gaussianVelocity η‖ ^ 2 := by
  have hs : 0 ≤ gaussianFrequencyK η / (2 * Real.pi) := div_nonneg hη (by positivity)
  simp only [gaussianPhaseMap, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hL, Real.sq_sqrt hs]
  field_simp

theorem gaussianPhaseMap_exponential {d : ℕ} (W : TransverseSpace d) (η : OAI.Analysis.Calculus.Current.SpatialSpace d)
    {L : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ gaussianFrequencyK η) :
    standardGaussian (Real.sqrt L • gaussianPhaseMap (W, η)) =
      Complex.exp (-(L / 2 * gaussianFrequencyK η * ‖W - gaussianVelocity η‖ ^ 2 : ℝ)) := by
  unfold standardGaussian
  congr 1
  rw [neg_mul, ← Complex.ofReal_pow, ← Complex.ofReal_mul, gaussianPhaseMap_norm_sq W η hL hη]

theorem gaussianPhaseMap_inverse_exponential {d : ℕ} (W : TransverseSpace d)
    (η : OAI.Analysis.Calculus.Current.SpatialSpace d) {L : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ gaussianFrequencyK η) :
    inverseStandardGaussian (Real.sqrt L • gaussianPhaseMap (W, η)) =
      Complex.exp ((L / 2 * gaussianFrequencyK η * ‖W - gaussianVelocity η‖ ^ 2 : ℝ)) := by
  unfold inverseStandardGaussian
  congr 1
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, gaussianPhaseMap_norm_sq W η hL hη]

theorem contDiffOn_sourceGaussian {d : ℕ} (W : TransverseSpace d) {L : ℝ} (hL : 0 ≤ L) :
    ContDiffOn ℝ ∞ (fun ξ : OAI.Analysis.Calculus.Current.SpatialSpace d => Complex.exp
      (-(L / 2 * gaussianFrequencyK ξ * ‖W - gaussianVelocity ξ‖ ^ 2 : ℝ)))
      {ξ | 0 < gaussianFrequencyK ξ} := by
  have hp : ContDiffOn ℝ ∞ (fun ξ : OAI.Analysis.Calculus.Current.SpatialSpace d => gaussianPhaseMap (W, ξ))
      {ξ | 0 < gaussianFrequencyK ξ} :=
    contDiffOn_gaussianPhaseMap.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
  apply (contDiff_standardGaussian.comp_contDiffOn (hp.const_smul (Real.sqrt L))).congr
  intro ξ hξ
  exact (gaussianPhaseMap_exponential W ξ hL hξ.le).symm

theorem contDiffOn_sourceInverseGaussian {d : ℕ} (W : TransverseSpace d) {L : ℝ} (hL : 0 ≤ L) :
    ContDiffOn ℝ ∞ (fun ξ : OAI.Analysis.Calculus.Current.SpatialSpace d => Complex.exp
      ((L / 2 * gaussianFrequencyK ξ * ‖W - gaussianVelocity ξ‖ ^ 2 : ℝ)))
      {ξ | 0 < gaussianFrequencyK ξ} := by
  have hp : ContDiffOn ℝ ∞ (fun ξ : OAI.Analysis.Calculus.Current.SpatialSpace d => gaussianPhaseMap (W, ξ))
      {ξ | 0 < gaussianFrequencyK ξ} :=
    contDiffOn_gaussianPhaseMap.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
  apply (contDiff_inverseStandardGaussian.comp_contDiffOn (hp.const_smul (Real.sqrt L))).congr
  intro ξ hξ
  exact (gaussianPhaseMap_inverse_exponential W ξ hL hξ.le).symm

/-- The exact forward exponential in the source has the sharp half-power
derivative loss, uniformly on any fixed compact positive-frequency sector. -/
theorem uniform_gaussian_phase_jets {d : ℕ} {S : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)}
    (hS : IsCompact S) (hSpos : ∀ η ∈ S, 0 < gaussianFrequencyK η)
    (w₀ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : TransverseSpace d, ‖W‖ ≤ w₀ →
      ∀ η ∈ S, ∀ L : ℝ, 1 ≤ L → ∀ n ≤ N,
      ‖iteratedFDeriv ℝ n (fun ξ => Complex.exp
        (-(L / 2 * gaussianFrequencyK ξ * ‖W - gaussianVelocity ξ‖ ^ 2 : ℝ))) η‖ ≤
        C * L ^ ((n : ℝ) / 2) := by
  have hU : IsOpen {p : TransverseSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK p.2} :=
    isOpen_lt continuous_const (continuous_gaussianFrequencyK.comp continuous_snd)
  obtain ⟨C, hC, hc⟩ := uniform_local_gaussian_jets
    (isCompact_closedBall (0 : TransverseSpace d) w₀) hS hU
    (fun p hp => hSpos p.2 hp.2) contDiffOn_gaussianPhaseMap N
  refine ⟨C, hC, ?_⟩
  intro W hW η hη L hL n hn
  have hs : 1 ≤ Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL
  have hb := hc W (by simpa using hW) η hη (Real.sqrt L) hs n hn
  rw [sqrt_pow_eq_half_rpow (by linarith)] at hb
  have hneigh : ∀ᶠ ξ in 𝓝 η, 0 < gaussianFrequencyK ξ :=
    (isOpen_lt continuous_const continuous_gaussianFrequencyK).mem_nhds (hSpos η hη)
  have he : (fun ξ => standardGaussian (Real.sqrt L • gaussianPhaseMap (W, ξ))) =ᶠ[𝓝 η]
      (fun ξ => Complex.exp (-(L / 2 * gaussianFrequencyK ξ * ‖W - gaussianVelocity ξ‖ ^ 2 : ℝ))) := by
    filter_upwards [hneigh] with ξ hξ
    exact gaussianPhaseMap_exponential W ξ (by linarith) hξ.le
  rwa [(he.iteratedFDeriv ℝ n).self_of_nhds] at hb

/-- The reciprocal exponential obeys the same derivative count on the
source observation patch `sqrt L * |W-v| ≤ R`. -/
theorem uniform_inverse_gaussian_phase_jets {d : ℕ} {S : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)}
    (hS : IsCompact S) (hSpos : ∀ η ∈ S, 0 < gaussianFrequencyK η)
    (w₀ R : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : TransverseSpace d, ‖W‖ ≤ w₀ →
      ∀ η ∈ S, ∀ L : ℝ, 1 ≤ L → Real.sqrt L * ‖W - gaussianVelocity η‖ ≤ R →
      ∀ n ≤ N,
      ‖iteratedFDeriv ℝ n (fun ξ => Complex.exp
        ((L / 2 * gaussianFrequencyK ξ * ‖W - gaussianVelocity ξ‖ ^ 2 : ℝ))) η‖ ≤
        C * L ^ ((n : ℝ) / 2) := by
  obtain ⟨A, hA⟩ := hS.exists_bound_of_continuousOn continuous_gaussianFrequencyK.continuousOn
  have hU : IsOpen {p : TransverseSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK p.2} :=
    isOpen_lt continuous_const (continuous_gaussianFrequencyK.comp continuous_snd)
  obtain ⟨C, hC, hc⟩ := uniform_local_inverse_gaussian_jets
    (isCompact_closedBall (0 : TransverseSpace d) w₀) hS hU
    (fun p hp => hSpos p.2 hp.2) contDiffOn_gaussianPhaseMap N
    (Real.sqrt (A / (2 * Real.pi)) * R)
  refine ⟨C, hC, ?_⟩
  intro W hW η hη L hL hR n hn
  have hs : 1 ≤ Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL
  have hkA : gaussianFrequencyK η ≤ A := (le_abs_self _).trans (hA η hη)
  have hbR : ‖Real.sqrt L • gaussianPhaseMap (W, η)‖ ≤ Real.sqrt (A / (2 * Real.pi)) * R := by
    simp only [gaussianPhaseMap, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ = Real.sqrt (gaussianFrequencyK η / (2 * Real.pi)) *
          (Real.sqrt L * ‖W - gaussianVelocity η‖) := by ring
      _ ≤ Real.sqrt (A / (2 * Real.pi)) * (Real.sqrt L * ‖W - gaussianVelocity η‖) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt
          (div_le_div_of_nonneg_right hkA (by positivity))) (by positivity)
      _ ≤ Real.sqrt (A / (2 * Real.pi)) * R :=
        mul_le_mul_of_nonneg_left hR (Real.sqrt_nonneg _)
  have hb := hc W (by simpa using hW) η hη (Real.sqrt L) hs hbR n hn
  rw [sqrt_pow_eq_half_rpow (by linarith)] at hb
  have hneigh : ∀ᶠ ξ in 𝓝 η, 0 < gaussianFrequencyK ξ :=
    (isOpen_lt continuous_const continuous_gaussianFrequencyK).mem_nhds (hSpos η hη)
  have he : (fun ξ => inverseStandardGaussian (Real.sqrt L • gaussianPhaseMap (W, ξ))) =ᶠ[𝓝 η]
      (fun ξ => Complex.exp ((L / 2 * gaussianFrequencyK ξ * ‖W - gaussianVelocity ξ‖ ^ 2 : ℝ))) := by
    filter_upwards [hneigh] with ξ hξ
    exact gaussianPhaseMap_inverse_exponential W ξ (by linarith) hξ.le
  rwa [(he.iteratedFDeriv ℝ n).self_of_nhds] at hb

end OAI.Analysis.PDE.Concentration
