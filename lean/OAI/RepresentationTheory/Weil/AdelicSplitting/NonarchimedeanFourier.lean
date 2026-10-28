import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierCompactDomain
import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierIntertwiner

/-! # Nonarchimedean Fourier -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanFourier.LocalAnalysis

noncomputable section

section

/-! Plancherel with the Fourier-square scalar, derived by Fubini. -/

open _root_.MeasureTheory
open scoped ENNReal

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
  (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ)
  (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]

include hu hc in
theorem fourierIntegral_scaled_norm_sq
    (hStable : ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n, Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k n)
    (c : ℝ) (hSquare : ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) x,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val) x = (c : ℂ) * f.val (-x))
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (∫ x, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x‖ ^ 2 ∂μ) = c * ∫ x, ‖f.val x‖ ^ 2 ∂μ := by
  have hf := TestSpace.LocalAnalysis.schwartzBruhat_integrable μ f
  have hg := TestSpace.LocalAnalysis.schwartzBruhat_integrable μ (FourierIntertwiner.LocalAnalysis.testFourierLinear ψ hu hc μ hStable f)
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
    (innerSL ℂ) (L := dotProductBilin k k)
    (FourierTools.LocalAnalysis.circleCharacter_continuous ψ hu hc) (FourierTools.LocalAnalysis.dotProductBilin_continuous n) hf hg
  have hneg (x : Local.FunctionsMetaplectic.Construction.Position k n) :
      VectorFourier.fourierIntegral (FourierTools.LocalAnalysis.circleCharacter ψ hu) μ
        (-(dotProductBilin k k).flip) (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val) x = (c : ℂ) * f.val x := by
    have hi := hSquare f (-x)
    rw [neg_neg] at hi
    rw [← hi]
    unfold VectorFourier.fourierIntegral Local.FunctionsMetaplectic.Construction.fourierIntegral
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      simp only [LinearMap.neg_apply, LinearMap.flip_apply,
        Circle.smul_def, smul_eq_mul]
      change ψ (- -Local.FunctionsMetaplectic.Construction.dot x y) * _ = _ * ψ (-Local.FunctionsMetaplectic.Construction.dot (-x) y)
      simp only [Local.FunctionsMetaplectic.Construction.dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]
      exact mul_comm _ _
  change (∫ x, @inner ℂ ℂ _
    (VectorFourier.fourierIntegral (FourierTools.LocalAnalysis.circleCharacter ψ hu) μ (dotProductBilin k k) f.val x)
    (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x) ∂μ) =
      ∫ x, @inner ℂ ℂ _ (f.val x)
        (VectorFourier.fourierIntegral (FourierTools.LocalAnalysis.circleCharacter ψ hu) μ
          (-(dotProductBilin k k).flip) (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val) x) ∂μ at h
  rw [← FourierTools.LocalAnalysis.fourierIntegral_eq_vectorFourier ψ hu] at h
  simp_rw [hneg] at h
  have hinner (z : ℂ) : @inner ℂ ℂ _ z ((c : ℂ) * z) =
      (c : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    change @inner ℂ ℂ _ z ((c : ℂ) • z) = _
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow]
  simp_rw [hinner] at h
  rw [integral_const_mul] at h
  simp_rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, integral_complex_ofReal] at h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_mul] using h

end

section

/-! Passing the test-function Fourier identity to L¹ ∩ L² limits. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology ENNReal

theorem L2_integral_norm_sq_general {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : Lp ℂ 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  rw [Lp.norm_def, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable f)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, invOf_eq_inv]
  rw [← Real.sqrt_eq_rpow]
  exact (Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg ‖f x‖))).symm

theorem toLp_norm_sq {E : Type*} [MeasurableSpace E]
    (μ : Measure E) {f : E → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← L2_integral_norm_sq_general]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
  (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ)
  (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]

include hu hc in
omit [LocallyCompactSpace k] [μ.IsAddHaarMeasure] in
theorem fourierIntegral_sub {f g : Local.FunctionsMetaplectic.Construction.Position k n → ℂ}
    (hf : Integrable f μ) (hg : Integrable g μ) (x : Local.FunctionsMetaplectic.Construction.Position k n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (f - g) x = Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x - Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ g x := by
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  rw [← integral_sub (FourierTools.LocalAnalysis.fourierKernel_integrable ψ hu hc μ hf x)
    (FourierTools.LocalAnalysis.fourierKernel_integrable ψ hu hc μ hg x)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => sub_mul (f y) (g y) _

include hu hc in
omit [LocallyCompactSpace k] [μ.IsAddHaarMeasure] in
theorem fourierIntegral_tendsto_of_L1
    {f : ℕ → Local.FunctionsMetaplectic.Construction.Position k n → ℂ} {g : Local.FunctionsMetaplectic.Construction.Position k n → ℂ}
    (hf : ∀ j, Integrable (f j) μ) (hg : Integrable g μ)
    (hfg : Tendsto (fun j => eLpNorm (f j - g) 1 μ) atTop (𝓝 0))
    (x : Local.FunctionsMetaplectic.Construction.Position k n) :
    Tendsto (fun j => Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (f j) x) atTop (𝓝 (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ g x)) := by
  have hbound : Tendsto (fun j => ∫ y, ‖f j y - g y‖ ∂μ) atTop (𝓝 0) := by
    have h := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hfg
    have he (j : ℕ) : (eLpNorm (f j - g) 1 μ).toReal = ∫ y, ‖f j y - g y‖ ∂μ := by
      rw [eLpNorm_one_eq_lintegral_enorm ((hf j).sub hg).aestronglyMeasurable]
      exact (integral_norm_eq_lintegral_enorm ((hf j).sub hg).aestronglyMeasurable).symm
    simpa only [Function.comp_def, he, ENNReal.toReal_zero] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hbound
  intro j
  rw [← fourierIntegral_sub ψ hu hc μ (hf j) hg x,
    FourierTools.LocalAnalysis.fourierIntegral_eq_vectorFourier ψ hu]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

def testToL2 : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (TestSpace.LocalAnalysis.schwartzBruhat_memLp μ 2 f.property).toLp f.val
  map_add' _ _ := MemLp.toLp_add _ _
  map_smul' c _ := MemLp.toLp_const_smul c _

omit [LocallyCompactSpace k] in
theorem testToL2_norm_sq (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    ‖testToL2 μ f‖ ^ 2 = ∫ x, ‖f.val x‖ ^ 2 ∂μ :=
  toLp_norm_sq μ (TestSpace.LocalAnalysis.schwartzBruhat_memLp μ 2 f.property)

omit [LocallyCompactSpace k] in
theorem testToL2_ae (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) : testToL2 μ f =ᵐ[μ] f.val :=
  MemLp.coeFn_toLp (TestSpace.LocalAnalysis.schwartzBruhat_memLp μ 2 f.property)

include hu hc in
omit [LocallyCompactSpace k] in
theorem fourier_L2_limit
    (hStable : ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n, Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k n)
    (c : ℝ) (hcpos : 0 < c)
    (hEnergy : ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n,
      (∫ x, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x‖ ^ 2 ∂μ) = c * ∫ x, ‖f.val x‖ ^ 2 ∂μ)
    (f : ℕ → Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) (g : Local.FunctionsMetaplectic.Construction.Position k n → ℂ)
    (hg1 : Integrable g μ) (hg2 : MemLp g 2 μ)
    (h1 : Tendsto (fun j => eLpNorm ((f j).val - g) 1 μ) atTop (𝓝 0))
    (h2 : Tendsto (fun j => eLpNorm ((f j).val - g) 2 μ) atTop (𝓝 0)) :
    MemLp (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ g) 2 μ ∧
      (∫ x, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ g x‖ ^ 2 ∂μ) = c * ∫ x, ‖g x‖ ^ 2 ∂μ := by
  let P := testToL2 (n := n) μ
  let T := FourierIntertwiner.LocalAnalysis.testFourierLinear ψ hu hc μ hStable
  let Q := P.comp T
  let p : Lp ℂ 2 μ := hg2.toLp g
  have hp : Tendsto (fun j => P (f j)) atTop (𝓝 p) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun j => (f j).val)
      (fun j => TestSpace.LocalAnalysis.schwartzBruhat_memLp μ 2 (f j).property) g hg2).mpr h2
  have hnorm (z : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) : ‖Q z‖ ^ 2 = c * ‖P z‖ ^ 2 := by
    change ‖testToL2 μ (T z)‖ ^ 2 = c * ‖testToL2 μ z‖ ^ 2
    rw [testToL2_norm_sq, testToL2_norm_sq]
    exact hEnergy z
  have hroot : 0 < Real.sqrt c := Real.sqrt_pos.mpr hcpos
  have hdist (z w : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
      ‖Q z - Q w‖ = Real.sqrt c * ‖P z - P w‖ := by
    have h := hnorm (z - w)
    rw [map_sub, map_sub] at h
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hroot.le (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hcpos.le]
    exact h
  have hqC : CauchySeq (fun j => Q (f j)) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hp.cauchySeq (ε / Real.sqrt c) (div_pos hε hroot)
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [dist_eq_norm, hdist, ← dist_eq_norm]
    simpa only [mul_comm] using (lt_div_iff₀ hroot).mp (hN i hi j hj)
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete hqC
  obtain ⟨s, hs, hsae⟩ := (tendstoInMeasure_of_tendsto_Lp hq).exists_seq_tendsto_ae
  have hQae (j : ℕ) : Q (f j) =ᵐ[μ] Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (f j).val := testToL2_ae μ (T (f j))
  have hpoint (x : Local.FunctionsMetaplectic.Construction.Position k n) :
      Tendsto (fun j => Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (f j).val x) atTop (𝓝 (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ g x)) :=
    fourierIntegral_tendsto_of_L1 ψ hu hc μ (fun j => TestSpace.LocalAnalysis.schwartzBruhat_integrable μ (f j)) hg1 h1 x
  have hae : q =ᵐ[μ] Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ g := by
    filter_upwards [hsae, ae_all_iff.mpr hQae] with x hx he
    apply tendsto_nhds_unique hx
    exact ((hpoint x).comp hs.tendsto_atTop).congr (fun j => (he (s j)).symm)
  have hqnorm : ‖q‖ ^ 2 = c * ‖p‖ ^ 2 :=
    tendsto_nhds_unique (hq.norm.pow 2)
      (((hp.norm.pow 2).const_mul c).congr (fun j => (hnorm (f j)).symm))
  refine ⟨(memLp_congr_ae hae).mp (Lp.memLp q), ?_⟩
  calc
    _ = ∫ x, ‖q x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      rw [hx]
    _ = ‖q‖ ^ 2 := L2_integral_norm_sq_general μ q
    _ = c * ‖p‖ ^ 2 := hqnorm
    _ = _ := congrArg (c * ·) (toLp_norm_sq μ hg2)

end

/-! Integral Cauchy–Schwarz with explicit L² energies. -/

open _root_.MeasureTheory
open scoped InnerProductSpace ComplexConjugate

theorem norm_integral_conj_mul_le_energy
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (a b : X → ℂ)
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    ‖∫ x, conj (a x) * b x ∂μ‖ ≤
      Real.sqrt (∫ x, ‖a x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖b x‖ ^ 2 ∂μ) := by
  have hp : (∫ x, conj (a x) * b x ∂μ) = ⟪ha.toLp a, hb.toLp b⟫_ℂ := by
    change _ = ∫ x, ⟪(ha.toLp a) x, (hb.toLp b) x⟫_ℂ ∂μ
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hax hbx
    rw [hax, hbx]
    exact mul_comm _ _
  rw [hp, ← toLp_norm_sq μ ha, ← toLp_norm_sq μ hb,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact norm_inner_le_norm _ _

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanFourier.LocalAnalysis
