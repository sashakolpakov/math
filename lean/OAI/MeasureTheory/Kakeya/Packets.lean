import OAI.MeasureTheory.Kakeya.Geometry
import OAI.Analysis.Fourier.Restriction.Basic

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace OAI.MeasureTheory.Kakeya

def packetCap {n : ℕ} (δ : ℝ) (v : Space n) : Set (Space n) :=
  {ω | ‖ω‖ = 1 ∧ ‖ω - v‖ ≤ δ / 32}

theorem measurableSet_packetCap {n : ℕ} (δ : ℝ) (v : Space n) :
    MeasurableSet (packetCap δ v) := by
  have hc : Continuous (fun ω : Space n ↦ ‖ω - v‖) := by fun_prop
  exact (isClosed_eq continuous_norm continuous_const).measurableSet.inter
    (isClosed_le hc continuous_const).measurableSet

theorem packetCaps_disjoint {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {v w : Space n} (hsep : δ ≤ dist v w) :
    Disjoint (packetCap δ v) (packetCap δ w) := by
  apply Set.disjoint_left.mpr
  intro ω hωv hωw
  have ht := dist_triangle v ω w
  have hv : dist v ω ≤ δ / 32 := by simpa only [dist_comm v ω, dist_eq_norm] using hωv.2
  have hw : dist ω w ≤ δ / 32 := by simpa only [dist_eq_norm] using hωw.2
  linarith

def capPacket {n : ℕ} (δ : ℝ) (v x : Space n) : Space n → ℂ :=
  (packetCap δ v).indicator (fun ω ↦
    Complex.exp (-Complex.I * ((inner ℝ x ω / δ ^ 2 : ℝ) : ℂ)))

theorem integrable_capPacket {n : ℕ} (δ : ℝ) (v x : Space n) :
    Integrable (capPacket δ v x) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  have hm : AEStronglyMeasurable
      (fun ω : Space n ↦ Complex.exp (-Complex.I * ((inner ℝ x ω / δ ^ 2 : ℝ) : ℂ)))
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by fun_prop
  apply Integrable.indicator _ (measurableSet_packetCap δ v)
  apply (integrable_const (1 : ℝ)).mono' hm
  exact Filter.Eventually.of_forall fun ω ↦ by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      neg_zero, zero_mul, mul_zero, sub_zero, Real.exp_zero, le_refl]

theorem norm_capPacket {n : ℕ} (δ : ℝ) (v x ω : Space n) :
    ‖capPacket δ v x ω‖ = (packetCap δ v).indicator (fun _ ↦ (1 : ℝ)) ω := by
  by_cases hω : ω ∈ packetCap δ v
  · simp only [capPacket, Set.indicator_of_mem hω, Complex.norm_exp, Complex.mul_re,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, neg_zero, zero_mul, mul_zero, sub_zero, Real.exp_zero]
  · simp [capPacket, hω]

theorem norm_mul_capPacket_rpow {n : ℕ} (δ : ℝ) (v x ω : Space n)
    (c : ℂ) {p : ℝ} (hp : 0 < p) :
    ‖c * capPacket δ v x ω‖ ^ p =
      (packetCap δ v).indicator (fun _ ↦ ‖c‖ ^ p) ω := by
  rw [norm_mul, norm_capPacket]
  by_cases hω : ω ∈ packetCap δ v <;> simp [hω, Real.zero_rpow hp.ne']

theorem integrable_norm_mul_capPacket_rpow {n : ℕ} (δ : ℝ) (v x : Space n)
    (c : ℂ) {p : ℝ} (hp : 0 < p) :
    Integrable (fun ω ↦ ‖c * capPacket δ v x ω‖ ^ p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  simp_rw [norm_mul_capPacket_rpow δ v x _ c hp]
  exact (integrable_const _).indicator (measurableSet_packetCap δ v)

theorem integral_norm_mul_capPacket_rpow {n : ℕ} (δ : ℝ) (v x : Space n)
    (c : ℂ) {p : ℝ} (hp : 0 < p) :
    (∫ ω, ‖c * capPacket δ v x ω‖ ^ p ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) =
      ‖c‖ ^ p * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ v) := by
  simp_rw [norm_mul_capPacket_rpow δ v x _ c hp]
  rw [integral_indicator (measurableSet_packetCap δ v), setIntegral_const]
  simp only [smul_eq_mul, mul_comm]

theorem packet_phase_factorization {n : ℕ} (δ : ℝ) (x y v ω : Space n) :
    Complex.exp (Complex.I * ((inner ℝ ((δ ^ 2)⁻¹ • y) ω : ℝ) : ℂ)) *
      Complex.exp (-Complex.I * ((inner ℝ x ω / δ ^ 2 : ℝ) : ℂ)) =
    Complex.exp (Complex.I * ((inner ℝ (y - x) v / δ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((inner ℝ (y - x) (ω - v) / δ ^ 2 : ℝ) : ℂ)) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [real_inner_smul_left, inner_sub_left, inner_sub_right]
  push_cast
  ring

/-- Modulation and spatial rescaling produce the cap integral with its
constant phase removed; the constant phase has norm one. -/
theorem norm_extension_capPacket {n : ℕ} (δ : ℝ) (v x y : Space n) :
    ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (capPacket δ v x) ((δ ^ 2)⁻¹ • y)‖ =
      ‖∫ ω in packetCap δ v,
        Complex.exp (Complex.I * ((inner ℝ (y - x) (ω - v) / δ ^ 2 : ℝ) : ℂ))
          ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n‖ := by
  have heq : OAI.Analysis.Fourier.Restriction.sphericalExtension (capPacket δ v x) ((δ ^ 2)⁻¹ • y) =
      Complex.exp (Complex.I * ((inner ℝ (y - x) v / δ ^ 2 : ℝ) : ℂ)) *
      ∫ ω in packetCap δ v,
        Complex.exp (Complex.I * ((inner ℝ (y - x) (ω - v) / δ ^ 2 : ℝ) : ℂ))
          ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
    calc
      OAI.Analysis.Fourier.Restriction.sphericalExtension (capPacket δ v x) ((δ ^ 2)⁻¹ • y) =
        ∫ ω in packetCap δ v,
          Complex.exp (Complex.I * ((inner ℝ ((δ ^ 2)⁻¹ • y) ω : ℝ) : ℂ)) *
          Complex.exp (-Complex.I * ((inner ℝ x ω / δ ^ 2 : ℝ) : ℂ)) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
            rw [OAI.Analysis.Fourier.Restriction.sphericalExtension, ← integral_indicator (measurableSet_packetCap δ v)]
            apply integral_congr_ae
            exact Eventually.of_forall fun ω ↦ by
              by_cases hω : ω ∈ packetCap δ v <;> simp [capPacket, hω]
      _ = _ := by
        simp_rw [packet_phase_factorization δ x y v]
        exact integral_const_mul _ _
  rw [heq, norm_mul]
  have hnorm : ‖Complex.exp (Complex.I * ((inner ℝ (y - x) v / δ ^ 2 : ℝ) : ℂ))‖ = 1 := by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, Real.exp_zero]
  rw [hnorm, one_mul]

/-- The wave packet is uniformly large throughout the radius-`2δ` tube.
This is the actual spherical extension operator, not an abstract packet axiom. -/
theorem cap_packet_lower_bound {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {v x y : Space n} (hv : ‖v‖ = 1) (hy : y ∈ OAI.MeasureTheory.Kakeya.tube (2 * δ) v x) :
    (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ v) / 2 ≤
      ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (capPacket δ v x) ((δ ^ 2)⁻¹ • y)‖ := by
  rcases mem_tube_iff.mp hy with ⟨t, ht, hyt⟩
  let z := y - (x + t • v)
  have hz : ‖z‖ ≤ 2 * δ := by simpa only [z, dist_eq_norm] using hyt.le
  have hyz : y - x = t • v + z := by dsimp [z]; abel
  have hsmall : ∀ᵐ ω ∂(OAI.Analysis.Fourier.Restriction.sphereMeasure n).restrict (packetCap δ v),
      |inner ℝ (y - x) (ω - v) / δ ^ 2| ≤ 1 / 4 := by
    filter_upwards [ae_restrict_mem (measurableSet_packetCap δ v)] with ω hω
    rw [hyz]
    exact (cap_packet_phase_bound_small hδ hω.1 hv (abs_le.mpr ht) hz hω.2).le
  have h := OAI.Analysis.Fourier.Restriction.small_phase_integral_lower_bound
    ((OAI.Analysis.Fourier.Restriction.sphereMeasure n).restrict (packetCap δ v))
    (fun ω ↦ inner ℝ (y - x) (ω - v) / δ ^ 2) (by fun_prop) hsmall
  rw [norm_extension_capPacket]
  simpa [Measure.real] using h

end OAI.MeasureTheory.Kakeya
