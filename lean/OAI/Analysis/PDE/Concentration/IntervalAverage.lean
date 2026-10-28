import OAI.Analysis.PDE.Green.ParametricSet

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set OAI.Analysis.PDE.Green
open scoped ContDiff Topology

section Smooth
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem contDiff_intervalAverage {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a ≤ b) :
    ContDiff ℝ ∞ (fun x => ∫ t in a..b, f (x, t)) := by
  have hh := OAI.Analysis.PDE.Green.contDiffOn_compact_setIntegral volume (K := Icc a b) (S := Ioc a b)
    isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self (by simp)
    isOpen_univ isOpen_univ f hf.contDiffOn (fun _ _ _ _ => mem_univ _)
  simp only [← intervalIntegral.integral_of_le hab] at hh
  exact contDiffOn_univ.mp hh

end Smooth

theorem deriv_intervalAverage {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    deriv (fun x => ∫ t in a..b, f (x, t)) x =
      ∫ t in a..b, deriv (fun y => f (y, t)) x := by
  let K := Icc a b
  let : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_Icc
  let ν : Measure K := (volume.restrict (Ioc a b)).comap Subtype.val
  have hh := OAI.Analysis.PDE.Green.hasFDerivAt_compact_parametric_integral (μ := ν) isOpen_univ isOpen_univ
    f hf.contDiffOn (fun t : K => (t : ℝ)) continuous_subtype_val
    (fun _ _ _ => mem_univ _) (mem_univ x)
  have hint (g : ℝ → ℝ) : (∫ t : K, g t ∂ν) = ∫ t in a..b, g t := by
    have h := integral_subtype_comap (s := Icc a b) (μ := volume.restrict (Ioc a b))
      measurableSet_Icc g
    simpa only [ν, K, Measure.restrict_restrict measurableSet_Icc,
      inter_eq_right.mpr Ioc_subset_Icc_self, intervalIntegral.integral_of_le hab] using! h
  have he : (fun y => ∫ t : K, f (y, t) ∂ν) = (fun y => ∫ t in a..b, f (y, t)) := by
    funext y
    exact hint (fun t => f (y, t))
  rw [he] at hh
  rw [hh.hasDerivAt.deriv]
  have hd : Continuous (fun t : K => OAI.Analysis.PDE.Green.partialFirstDerivative f (x, t)) := by
    exact ((contDiffOn_univ.mp (OAI.Analysis.PDE.Green.contDiffOn_partialFirstDerivative isOpen_univ hf.contDiffOn)).continuous).comp
      (continuous_const.prodMk continuous_subtype_val)
  rw [ContinuousLinearMap.integral_apply
    (hd.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  rw [← hint]
  apply integral_congr_ae
  filter_upwards [] with t
  exact (OAI.Analysis.PDE.Green.hasFDerivAt_first_section isOpen_univ hf.contDiffOn x t (mem_univ _)).hasDerivAt.deriv.symm

theorem contDiff_firstPartial {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (fun x => f (x, p.2)) p.1) := by
  have he : (fun p : ℝ × ℝ => deriv (fun x => f (x, p.2)) p.1) =
      (fun p => OAI.Analysis.PDE.Green.partialFirstDerivative f p 1) := by
    funext p
    exact (OAI.Analysis.PDE.Green.hasFDerivAt_first_section isOpen_univ hf.contDiffOn p.1 p.2 (mem_univ _)).hasDerivAt.deriv
  rw [he]
  exact (contDiffOn_univ.mp (OAI.Analysis.PDE.Green.contDiffOn_partialFirstDerivative isOpen_univ hf.contDiffOn)).clm_apply contDiff_const

theorem continuous_firstPartial_slice {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    Continuous (fun t => deriv (fun y => f (y, t)) x) :=
  (contDiff_firstPartial hf).continuous.comp (continuous_const.prodMk continuous_id)

theorem continuous_secondPartial_slice {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    Continuous (fun t => deriv (deriv (fun y => f (y, t))) x) :=
  (contDiff_firstPartial (contDiff_firstPartial hf)).continuous.comp (continuous_const.prodMk continuous_id)

theorem second_deriv_intervalAverage {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    deriv (deriv (fun x => ∫ t in a..b, f (x, t))) x =
      ∫ t in a..b, deriv (deriv (fun y => f (y, t))) x := by
  have he : deriv (fun x => ∫ t in a..b, f (x, t)) =
      (fun x => ∫ t in a..b, deriv (fun y => f (y, t)) x) := by
    funext x
    exact deriv_intervalAverage hf hab x
  rw [he, deriv_intervalAverage (contDiff_firstPartial hf) hab]

theorem deriv_weighted_intervalAverage {f : ℝ × ℝ → ℝ} {w : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hw : ContDiff ℝ ∞ w)
    {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    deriv (fun x => ∫ t in a..b, w t * f (x, t)) x =
      ∫ t in a..b, w t * deriv (fun y => f (y, t)) x := by
  have hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => w p.2 * f p) :=
    (hw.comp contDiff_snd).mul hf
  rw [deriv_intervalAverage hF hab]
  apply intervalIntegral.integral_congr
  intro t _
  exact deriv_const_mul (w t)
    ((hf.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) x)

theorem second_deriv_weighted_intervalAverage {f : ℝ × ℝ → ℝ} {w : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hw : ContDiff ℝ ∞ w)
    {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    deriv (deriv (fun x => ∫ t in a..b, w t * f (x, t))) x =
      ∫ t in a..b, w t * deriv (deriv (fun y => f (y, t))) x := by
  have he : deriv (fun x => ∫ t in a..b, w t * f (x, t)) =
      (fun x => ∫ t in a..b, w t * deriv (fun y => f (y, t)) x) := by
    funext x
    exact deriv_weighted_intervalAverage hf hw hab x
  rw [he, deriv_weighted_intervalAverage (contDiff_firstPartial hf) hw hab]

end OAI.Analysis.PDE.Concentration
