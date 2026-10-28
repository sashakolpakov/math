import OAI.Analysis.PDE.Weak.Elliptic.H1
import OAI.Analysis.PDE.Weak.Elliptic.Multiplier
import OAI.Analysis.PDE.Variational.Poincare

noncomputable section
open Set _root_.MeasureTheory
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational OAI.Analysis.PDE.Green

variable {m : ℕ}

theorem cell_weighted_energy_lower
    (a b : OAI.Analysis.PDE.Variational.CellCoordinates m) (hab : a ≤ b) (j : Fin (m + 1))
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hu : ContDiff ℝ 1 u)
    (hzero : ∀ y ∈ Icc (a ∘ j.succAbove) (b ∘ j.succAbove),
      u (j.insertNth (a j) y) = 0) :
    (∫ x in Icc a b, u x ^ 2) =
      -(∫ x in Icc a b, 2 * u x * (x j - b j) * fderiv ℝ u x (Pi.single j 1)) := by
  let F : Fin (m + 1) → OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ :=
    fun i x ↦ if i = j then x j - b j else 0
  have hF : ∀ i, ContDiff ℝ 1 (F i) := by
    intro i
    by_cases hi : i = j
    · subst i
      simpa [F] using (contDiff_apply ℝ ℝ j).sub
        (contDiff_const : ContDiff ℝ 1 (fun _ : OAI.Analysis.PDE.Variational.CellCoordinates m ↦ b j))
    · simpa only [F, ite_eq_right hi] using
        (contDiff_const : ContDiff ℝ 1 (fun _ : OAI.Analysis.PDE.Variational.CellCoordinates m ↦ (0 : ℝ)))
  have hdF (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
      (∑ i, fderiv ℝ (F i) x (Pi.single i 1)) = 1 := by
    have hj : HasFDerivAt (F j)
        (ContinuousLinearMap.proj j : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] ℝ) x := by
      simpa [F] using
        (ContinuousLinearMap.proj j : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] ℝ).hasFDerivAt.sub_const (b j)
    rw [Finset.sum_eq_single j]
    · rw [hj.fderiv]
      simp
    · intro i _ hij
      simp [F, hij]
    · simp
  have hdu (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
      fderiv ℝ (fun y ↦ u y ^ 2) x (Pi.single j 1) =
        2 * u x * fderiv ℝ u x (Pi.single j 1) := by
    rw [((hu.differentiable one_ne_zero x).hasFDerivAt.pow 2).fderiv]
    simp
  have hid := OAI.Analysis.PDE.Green.integral_product_divergence_box a b hab F hF (hu.pow 2) (by
    intro i y hy
    by_cases hij : i = j
    · subst i
      simp [F, hzero y hy]
    · simp [F, hij])
  simp only [hdF, mul_one] at hid
  convert hid using 2
  congr 1
  funext x
  simp only [F, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hdu]
  ring

theorem cell_poincare_lower
    (a b : OAI.Analysis.PDE.Variational.CellCoordinates m) (hab : a ≤ b) (j : Fin (m + 1))
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hu : ContDiff ℝ 1 u)
    (hzero : ∀ y ∈ Icc (a ∘ j.succAbove) (b ∘ j.succAbove),
      u (j.insertNth (a j) y) = 0) :
    (∫ x in Icc a b, u x ^ 2) ≤
      4 * (b j - a j) ^ 2 * (∫ x in Icc a b, (fderiv ℝ u x (Pi.single j 1)) ^ 2) := by
  let d := fun x ↦ fderiv ℝ u x (Pi.single j 1)
  have hd : Continuous d := OAI.Analysis.PDE.Green.continuous_directional hu (Pi.single j 1)
  have hsq : IntegrableOn (fun x ↦ u x ^ 2) (Icc a b) :=
    (hu.continuous.pow 2).integrableOn_Icc
  have hdsq : IntegrableOn (fun x ↦ d x ^ 2) (Icc a b) := (hd.pow 2).integrableOn_Icc
  have hw : IntegrableOn (fun x ↦ -(2 * u x * (x j - b j) * d x)) (Icc a b) :=
    ((((continuous_const.mul hu.continuous).mul ((continuous_apply j).sub continuous_const)).mul
      hd).neg).integrableOn_Icc
  have hbnd (x : OAI.Analysis.PDE.Variational.CellCoordinates m) (hx : x ∈ Icc a b) :
      -(2 * u x * (x j - b j) * d x) ≤
        (1 / 2 : ℝ) * u x ^ 2 + 2 * (b j - a j) ^ 2 * d x ^ 2 := by
    have ht : 0 ≤ b j - x j := sub_nonneg.mpr (hx.2 j)
    have htL : b j - x j ≤ b j - a j := sub_le_sub_left (hx.1 j) _
    have hL : (x j - b j) ^ 2 ≤ (b j - a j) ^ 2 := by
      nlinarith [pow_le_pow_left₀ ht htL 2]
    have hs := sq_nonneg (u x + 2 * (x j - b j) * d x)
    have hm := mul_le_mul_of_nonneg_right hL (sq_nonneg (d x))
    nlinarith
  have hi := setIntegral_mono_on hw
    ((hsq.const_mul (1 / 2 : ℝ)).add (hdsq.const_mul (2 * (b j - a j) ^ 2)))
    measurableSet_Icc hbnd
  simp only [Pi.add_apply] at hi
  rw [integral_neg, ← cell_weighted_energy_lower a b hab j hu hzero,
    integral_add (hsq.const_mul (1 / 2 : ℝ))
      (hdsq.const_mul (2 * (b j - a j) ^ 2)), integral_const_mul, integral_const_mul] at hi
  change (∫ x in Icc a b, u x ^ 2) ≤
    4 * (b j - a j) ^ 2 * (∫ x in Icc a b, d x ^ 2)
  linarith

section Indicator
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X}

def indicatorL2 (s : Set X) (hs : MeasurableSet s) : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  fieldMultiplierCLM (s.indicator fun _ ↦ ContinuousLinearMap.id ℝ E)
    (aestronglyMeasurable_const.indicator hs)
    (ae_of_all _ fun x ↦ by
      by_cases hx : x ∈ s
      · simpa only [indicator_of_mem hx] using ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)
      · simp only [indicator_of_notMem hx, norm_zero, zero_le_one])

theorem indicatorL2_ae (s : Set X) (hs : MeasurableSet s) (u : Lp E 2 μ) :
    indicatorL2 s hs u =ᵐ[μ] s.indicator u := by
  filter_upwards [fieldMultiplierCLM_ae (s.indicator fun _ ↦ ContinuousLinearMap.id ℝ E)
    (aestronglyMeasurable_const.indicator hs) (M := 1)
    (ae_of_all _ fun x ↦ by
      by_cases hx : x ∈ s
      · simpa only [indicator_of_mem hx] using ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)
      · simp only [indicator_of_notMem hx, norm_zero, zero_le_one]) u] with x hx
  rw [show indicatorL2 s hs u x = (s.indicator fun _ ↦ ContinuousLinearMap.id ℝ E) x (u x) from hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

end Indicator

section IndicatorEnergy
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {μ : Measure X}

theorem norm_sq_indicatorL2
    (s : Set X) (hs : MeasurableSet s) (u : Lp E 2 μ) :
    ‖indicatorL2 s hs u‖ ^ 2 = ∫ x in s, ‖u x‖ ^ 2 ∂μ := by
  have hn : ‖indicatorL2 s hs u‖ ^ 2 = ∫ x, ‖indicatorL2 s hs u x‖ ^ 2 ∂μ := by
    simpa only [Lp.toLp_coeFn] using OAI.Analysis.PDE.Variational.norm_sq_toLp_eq_integral (Lp.memLp (indicatorL2 s hs u))
  rw [hn]
  calc
    _ = ∫ x, s.indicator (fun y ↦ ‖u y‖ ^ 2) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [indicatorL2_ae s hs u] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    _ = _ := integral_indicator hs
end IndicatorEnergy

theorem H1Zero.strip_energy
    (j : Fin (m + 1)) {p : H1Pair m} (hp : p ∈ H1Zero {x | 0 < x j})
    (a b : OAI.Analysis.PDE.Variational.CellCoordinates m) (hab : a ≤ b) (ha : a j = 0) :
    (∫ x in Icc a b, (p.1 x) ^ 2) ≤ 4 * (b j) ^ 2 * ‖p.2‖ ^ 2 := by
  have hc : IsClosed {q : H1Pair m |
      ‖indicatorL2 (Icc a b) measurableSet_Icc q.1‖ ^ 2 ≤ 4 * (b j) ^ 2 * ‖q.2‖ ^ 2} :=
    isClosed_le (((indicatorL2 (Icc a b) measurableSet_Icc).continuous.comp continuous_fst).norm.pow 2)
      (continuous_const.mul (continuous_snd.norm.pow 2))
  have hbound : ‖indicatorL2 (Icc a b) measurableSet_Icc p.1‖ ^ 2 ≤
      4 * (b j) ^ 2 * ‖p.2‖ ^ 2 := by
    apply closure_minimal (s := smoothH1Graph {x | 0 < x j}) _ hc hp
    rintro q ⟨u, hu, hs, hsub, rfl⟩
    change ‖indicatorL2 (Icc a b) measurableSet_Icc (smoothH1Pair u hu hs).1‖ ^ 2 ≤ _
    rw [norm_sq_indicatorL2]
    have hv : (∫ x in Icc a b, ‖(smoothH1Pair u hu hs).1 x‖ ^ 2) =
        ∫ x in Icc a b, u x ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (smoothH1Pair_value_ae u hu hs)] with x hx
      simp only [hx, Real.norm_eq_abs, sq_abs]
    rw [hv]
    have hz : ∀ y ∈ Icc (a ∘ j.succAbove) (b ∘ j.succAbove),
        u (j.insertNth (a j) y) = 0 := by
      intro y _
      apply image_eq_zero_of_notMem_tsupport
      intro h
      have hh := hsub h
      simp [ha] at hh
    have hP := cell_poincare_lower a b hab j (hu.of_le (by simp)) hz
    rw [ha, sub_zero] at hP
    refine hP.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hd : Integrable (fun x ↦ ‖OAI.Analysis.PDE.Variational.cellGradient u x‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm
        ((OAI.Analysis.PDE.Variational.continuous_cellGradient (hu.of_le (by simp))).aestronglyMeasurable)).mp
        ((OAI.Analysis.PDE.Variational.continuous_cellGradient (hu.of_le (by simp))).memLp_of_hasCompactSupport
          (hasCompactSupport_cellGradient hs))
    calc
      _ ≤ ∫ x in Icc a b, ‖OAI.Analysis.PDE.Variational.cellGradient u x‖ ^ 2 := by
        apply setIntegral_mono_on
          ((OAI.Analysis.PDE.Green.continuous_directional (hu.of_le (by simp)) _).pow 2).integrableOn_Icc
          hd.integrableOn measurableSet_Icc
        intro x _
        simpa only [Real.norm_eq_abs, sq_abs, OAI.Analysis.PDE.Variational.cellGradient, WithLp.ofLp_toLp, Pi.pow_apply] using
          pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (OAI.Analysis.PDE.Variational.cellGradient u x) j) 2
      _ ≤ ∫ x, ‖OAI.Analysis.PDE.Variational.cellGradient u x‖ ^ 2 :=
        setIntegral_le_integral hd (ae_of_all _ fun x ↦ sq_nonneg _)
      _ = ‖(smoothH1Pair u hu hs).2‖ ^ 2 := by
        symm
        exact OAI.Analysis.PDE.Variational.norm_sq_toLp_eq_integral
          ((OAI.Analysis.PDE.Variational.continuous_cellGradient (hu.of_le (by simp))).memLp_of_hasCompactSupport
            (hasCompactSupport_cellGradient hs))
  rw [norm_sq_indicatorL2] at hbound
  simpa only [Real.norm_eq_abs, sq_abs] using hbound

end OAI.Analysis.PDE.Weak
