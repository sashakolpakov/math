import OAI.RepresentationTheory.Weil.Local.RealCharacters

/-! # Archimedean Test Space -/

namespace OAI.RepresentationTheory.Weil.Local.ArchimedeanTestSpace.Construction

noncomputable section

section

/-! Archimedean Schwartz realization and quadratic stability at the complex place. -/

theorem schwartzBruhat_archimedean_iff
    {k : Type} [NormedField k] [NormedSpace ℝ k] [FiniteDimensional ℝ k]
    {n : ℕ} {f : FunctionsMetaplectic.Construction.Position k n → ℂ} :
    f ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n ↔ ∃ φ : SchwartzMap (FunctionsMetaplectic.Construction.Position k n) ℂ, f = φ := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        rcases hf with hf | ⟨d, e, φ, rfl⟩
        · exact ⟨hf.2.toSchwartzMap (RealTestSpace.Construction.locallyConstant_contDiff hf.1), rfl⟩
        · let a := e.symm.toAddEquiv.toRealLinearEquiv e.symm.continuous e.continuous
          exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ a φ, rfl⟩
    | zero => exact ⟨0, rfl⟩
    | add f g _ _ hf hg =>
        obtain ⟨φ, rfl⟩ := hf
        obtain ⟨χ, rfl⟩ := hg
        exact ⟨φ + χ, rfl⟩
    | smul c f _ hf =>
        obtain ⟨φ, rfl⟩ := hf
        exact ⟨c • φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    let e : (Fin (Module.finrank ℝ (FunctionsMetaplectic.Construction.Position k n)) → ℝ) ≃L[ℝ] FunctionsMetaplectic.Construction.Position k n :=
      ContinuousLinearEquiv.ofFinrankEq (by simp)
    have h := FunctionsMetaplectic.Construction.schwartz_coordinate_mem e.toContinuousAddEquiv
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ)
    convert h using 1
    funext x
    exact congrArg φ (e.apply_symm_apply x).symm

theorem quadratic_archimedean_temperate
    {k : Type} [NormedField k] [NormedAlgebra ℝ k] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) k) : Function.HasTemperateGrowth (FunctionsMetaplectic.Construction.quadratic B) := by
  have hc (i : Fin n) : Function.HasTemperateGrowth (fun x : FunctionsMetaplectic.Construction.Position k n => x i) :=
    (ContinuousLinearMap.proj i : FunctionsMetaplectic.Construction.Position k n →L[ℝ] k).hasTemperateGrowth
  have hq : Function.HasTemperateGrowth (fun x : FunctionsMetaplectic.Construction.Position k n => ∑ i, ∑ j, x i * B i j * x j) :=
    .sum (fun i _ => .sum (fun j _ => ((hc i).mul (.const (B i j))).mul (hc j)))
  have heq : FunctionsMetaplectic.Construction.quadratic B =
      (fun x : FunctionsMetaplectic.Construction.Position k n => ∑ i, ∑ j, x i * B i j * x j) * (fun _ => (2 : k)⁻¹) := by
    funext x
    exact div_eq_mul_inv _ _
  rw [heq]
  exact hq.mul (.const (2 : k)⁻¹)

theorem quadratic_archimedean_mem
    {k : Type} [NormedField k] [NormedAlgebra ℝ k] [FiniteDimensional ℝ k] {n : ℕ}
    (ψ : AddChar k ℂ) (hψ : Function.HasTemperateGrowth (fun t => ψ t))
    (B : Matrix (Fin n) (Fin n) k) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n := by
  obtain ⟨φ, hφ⟩ := schwartzBruhat_archimedean_iff.mp f.property
  rw [hφ]
  let χ := SchwartzMap.smulLeftCLM ℂ (fun x => ψ (FunctionsMetaplectic.Construction.quadratic B x)) φ
  refine schwartzBruhat_archimedean_iff.mpr ⟨χ, ?_⟩
  funext x
  exact (SchwartzMap.smulLeftCLM_apply_apply
    (hψ.comp (quadratic_archimedean_temperate B)) φ x).symm

theorem continuous_unitary_complex_character
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z)) (hu : ∀ z, ‖ψ z‖ = 1) :
    ∃ a b : ℝ, ∀ z : ℂ, ψ z = Gaussian.Construction.realCharacter a z.re * Gaussian.Construction.realCharacter b z.im := by
  let r : AddChar ℝ ℂ := ψ.compAddMonoidHom Complex.ofRealHom.toAddMonoidHom
  let i : AddChar ℝ ℂ := ψ.compAddMonoidHom
    ((AddMonoidHom.mulRight Complex.I).comp Complex.ofRealHom.toAddMonoidHom)
  have hr : Continuous (fun t => r t) := hc.comp Complex.continuous_ofReal
  have hi : Continuous (fun t => i t) := hc.comp (Complex.continuous_ofReal.mul_const Complex.I)
  obtain ⟨a, ha⟩ := RealCharacters.Construction.continuous_unitary_real_character r hr (fun t => hu (t : ℂ))
  obtain ⟨b, hb⟩ := RealCharacters.Construction.continuous_unitary_real_character i hi (fun t => hu ((t : ℂ) * Complex.I))
  refine ⟨a, b, fun z => ?_⟩
  rw [← ha, ← hb]
  change ψ z = ψ (z.re : ℂ) * ψ ((z.im : ℂ) * Complex.I)
  rw [← ψ.map_add_eq_mul, Complex.re_add_im]

theorem continuous_unitary_complex_character_temperate
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z)) (hu : ∀ z, ‖ψ z‖ = 1) :
    Function.HasTemperateGrowth (fun z => ψ z) := by
  obtain ⟨a, b, h⟩ := continuous_unitary_complex_character ψ hc hu
  have heq : (fun z => ψ z) = fun z => Gaussian.Construction.realCharacter a z.re * Gaussian.Construction.realCharacter b z.im := funext h
  rw [heq]
  exact ((RealTestSpace.Construction.realCharacter_temperate a).comp Complex.reCLM.hasTemperateGrowth).mul
    ((RealTestSpace.Construction.realCharacter_temperate b).comp Complex.imCLM.hasTemperateGrowth)

def complexQuadraticMetaplectic {n : ℕ}
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z)) (hu : ∀ z, ‖ψ z‖ = 1)
    (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℂ n) : FunctionsMetaplectic.Construction.Metaplectic ℂ n ψ :=
  QuadraticIntertwiner.Construction.quadraticMetaplectic ψ hu
    (quadratic_archimedean_mem ψ (continuous_unitary_complex_character_temperate ψ hc hu)) B

theorem complexQuadraticMetaplectic_projection {n : ℕ}
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z)) (hu : ∀ z, ‖ψ z‖ = 1)
    (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℂ n) :
    FunctionsMetaplectic.Construction.metaplecticProjection ℂ n ψ (complexQuadraticMetaplectic ψ hc hu B) =
      Generators.Construction.quadraticSymplectic B := rfl

theorem complexQuadraticMetaplectic_apply {n : ℕ}
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z)) (hu : ∀ z, ‖ψ z‖ = 1)
    (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℂ n) (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    (FunctionsMetaplectic.Construction.weilRepresentation ℂ n ψ (complexQuadraticMetaplectic ψ hc hu B) f).val x =
      ψ (FunctionsMetaplectic.Construction.quadratic B.val x) * f.val x := rfl

end

/-! Oscillatory Gaussian limits at the complex place. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology ComplexConjugate NNReal

def complexStandardCharacter : AddChar ℂ ℂ :=
  (Gaussian.Construction.realCharacter 1).compAddMonoidHom Complex.reCLM.toLinearMap.toAddMonoidHom

theorem realDampedGaussian_conj (c a ε : ℝ) :
    conj (Gaussian.Construction.realDampedGaussian c a ε) = Gaussian.Construction.realDampedGaussian c (-a) ε := by
  unfold Gaussian.Construction.realDampedGaussian
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [map_mul, Complex.conj_ofReal, Gaussian.Construction.realCharacter_apply, Gaussian.Construction.realCharacter_apply, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring

theorem realDampedGaussian_standard_tendsto :
    Tendsto (Gaussian.Construction.realDampedGaussian 1 1) (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.I ^ (1 / 2 : ℂ))) := by
  have hr : (Gaussian.Construction.realReferenceHaarFactor : ℂ) ≠ 0 := by
    exact_mod_cast Gaussian.Construction.realReferenceHaarFactor_pos.ne'
  have h := (Gaussian.Construction.regularizedGaussian_real_tendsto 1 1 (by norm_num) (by norm_num)).const_mul
    (Gaussian.Construction.realReferenceHaarFactor : ℂ)⁻¹
  simp only [Complex.ofReal_one, mul_one, div_one, ← mul_assoc, inv_mul_cancel₀ hr, one_mul] at h
  apply h.congr
  intro ε
  rw [Gaussian.Construction.regularizedGaussian_real, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]

def complexReferenceHaarFactor : ℝ≥0 :=
  Measure.addHaarScalarFactor (Measure.addHaar : Measure ℂ) volume

theorem complexReferenceHaarFactor_pos : 0 < complexReferenceHaarFactor :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem regularizedGaussian_complex_standard (ε : ℝ) :
    FunctionsMetaplectic.Construction.regularizedGaussian ℂ complexStandardCharacter 1 ε =
      (complexReferenceHaarFactor : ℂ) *
        (Gaussian.Construction.realDampedGaussian 1 1 ε * conj (Gaussian.Construction.realDampedGaussian 1 1 ε)) := by
  unfold FunctionsMetaplectic.Construction.regularizedGaussian
  rw [Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.addHaar : Measure ℂ) volume,
    integral_smul_nnreal_measure]
  change (complexReferenceHaarFactor : ℂ) * _ = _
  congr 1
  rw [← Complex.volume_preserving_equiv_real_prod.symm.integral_comp
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  rw [realDampedGaussian_conj]
  unfold Gaussian.Construction.realDampedGaussian
  rw [← integral_prod_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p : ℝ × ℝ => by
    dsimp only
    have hnorm : ‖Complex.measurableEquivRealProd.symm p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply, pow_two]
    rw [hnorm]
    change (Real.exp (-ε * (p.1 ^ 2 + p.2 ^ 2)) : ℂ) *
        Gaussian.Construction.realCharacter 1 ((1 * (Complex.measurableEquivRealProd.symm p) ^ 2 / 2).re) = _
    have hphase : (1 * (Complex.measurableEquivRealProd.symm p) ^ 2 / 2).re =
        1 * p.1 ^ 2 / 2 + -1 * p.2 ^ 2 / 2 := by
      simp [pow_two, Complex.measurableEquivRealProd_symm_apply]
      ring
    rw [hphase, (Gaussian.Construction.realCharacter 1).map_add_eq_mul]
    have he : Real.exp (-ε * (p.1 ^ 2 + p.2 ^ 2)) =
        Real.exp (-ε * p.1 ^ 2) * Real.exp (-ε * p.2 ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he, Complex.ofReal_mul]
    simp only [Real.norm_eq_abs, sq_abs]
    ring

theorem regularizedGaussian_complex_standard_tendsto :
    Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian ℂ complexStandardCharacter 1) (𝓝[>] (0 : ℝ))
      (𝓝 (complexReferenceHaarFactor : ℂ)) := by
  have h := (realDampedGaussian_standard_tendsto.mul
    ((Complex.continuous_conj.tendsto _).comp realDampedGaussian_standard_tendsto)).const_mul
      (complexReferenceHaarFactor : ℂ)
  have hsq : (Complex.I ^ (1 / 2 : ℂ)) ^ (2 : ℕ) = Complex.I := by simp [one_div]
  have hn : ‖Complex.I ^ (1 / 2 : ℂ)‖ ^ 2 = 1 := by
    simpa only [norm_pow, Complex.norm_I] using congrArg norm hsq
  have hprod : Complex.I ^ (1 / 2 : ℂ) * conj (Complex.I ^ (1 / 2 : ℂ)) = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, hn]
    rfl
  rw [hprod, mul_one] at h
  apply h.congr
  intro ε
  exact (regularizedGaussian_complex_standard ε).symm

theorem gaussianIntegral_complex_standard :
    FunctionsMetaplectic.Construction.gaussianIntegral ℂ complexStandardCharacter 1 = complexReferenceHaarFactor :=
  regularizedGaussian_complex_standard_tendsto.limUnder_eq

theorem gaussianIndex_complex_standard : FunctionsMetaplectic.Construction.gaussianIndex ℂ complexStandardCharacter 1 = 1 := by
  rw [FunctionsMetaplectic.Construction.gaussianIndex, gaussianIntegral_complex_standard]
  exact Gaussian.Construction.phase_positive_real _ complexReferenceHaarFactor_pos

theorem complex_character_coefficient
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z)) (hu : ∀ z, ‖ψ z‖ = 1) :
    ∃ b : ℂ, ∀ z : ℂ, ψ z = complexStandardCharacter (b * z) := by
  obtain ⟨r, s, h⟩ := continuous_unitary_complex_character ψ hc hu
  refine ⟨(r : ℂ) - (s : ℂ) * Complex.I, fun z => ?_⟩
  rw [h]
  change Gaussian.Construction.realCharacter r z.re * Gaussian.Construction.realCharacter s z.im =
    Gaussian.Construction.realCharacter 1 ((((r : ℂ) - (s : ℂ) * Complex.I) * z).re)
  rw [Gaussian.Construction.realCharacter_apply, Gaussian.Construction.realCharacter_apply, Gaussian.Construction.realCharacter_apply, ← Complex.exp_add]
  congr 1
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, sub_zero,
    Complex.sub_im, Complex.mul_im, mul_one, zero_sub]
  push_cast
  ring

def complexScalarAddEquiv (s : ℂ) (hs : s ≠ 0) : ℂ ≃ₜ+ ℂ :=
  (LinearEquiv.smulOfNeZero ℂ (M := ℂ) s hs).toContinuousLinearEquiv.toContinuousAddEquiv

theorem integral_complex_substitution (s : ℂ) (hs : s ≠ 0) (f : ℂ → ℂ) :
    (∫ z, f z ∂(Measure.addHaar : Measure ℂ)) =
      (addEquivAddHaarChar (complexScalarAddEquiv s hs) : ℂ) *
        ∫ z, f (s * z) ∂(Measure.addHaar : Measure ℂ) := by
  let e := complexScalarAddEquiv s hs
  let μ : Measure ℂ := Measure.addHaar
  calc
    _ = ∫ z, f z ∂(addEquivAddHaarChar e • μ.map e) := by
      rw [addEquivAddHaarChar_smul_map μ e]
    _ = _ := by
      rw [integral_smul_nnreal_measure]
      have he : (∫ z, f z ∂μ.map e) = ∫ z, f (e z) ∂μ :=
        integral_map_equiv e.toHomeomorph.toMeasurableEquiv f
      rw [he]
      rfl

theorem regularizedGaussian_complex_substitution
    (ψ : AddChar ℂ ℂ) (a s : ℂ) (hs : s ≠ 0)
    (hphase : ∀ z : ℂ, ψ (a * (s * z) ^ 2 / 2) = complexStandardCharacter (z ^ 2 / 2))
    (ε : ℝ) :
    FunctionsMetaplectic.Construction.regularizedGaussian ℂ ψ a ε =
      (addEquivAddHaarChar (complexScalarAddEquiv s hs) : ℂ) *
        FunctionsMetaplectic.Construction.regularizedGaussian ℂ complexStandardCharacter 1 (ε * ‖s‖ ^ 2) := by
  unfold FunctionsMetaplectic.Construction.regularizedGaussian
  rw [integral_complex_substitution s hs]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    dsimp only
    rw [hphase, one_mul, norm_mul, mul_pow]
    congr 2
    ring_nf

theorem complex_gaussian_limit_positive
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z)) (hu : ∀ z, ‖ψ z‖ = 1)
    (hn : ∃ z, ψ z ≠ 1) (a : ℂ) (ha : a ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian ℂ ψ a) (𝓝[>] (0 : ℝ)) (𝓝 (r : ℂ)) := by
  obtain ⟨b, hb⟩ := complex_character_coefficient ψ hc hu
  have hb0 : b ≠ 0 := by
    rintro rfl
    obtain ⟨z, hz⟩ := hn
    apply hz
    rw [hb, zero_mul, complexStandardCharacter.map_zero_eq_one]
  let s : ℂ := ((b * a)⁻¹) ^ (1 / 2 : ℂ)
  have hsq : s ^ (2 : ℕ) = (b * a)⁻¹ := by simp [s, one_div]
  have hs : s ≠ 0 := by
    intro hs
    have h := hsq
    rw [hs, zero_pow (by decide)] at h
    exact (inv_ne_zero (mul_ne_zero hb0 ha)) h.symm
  have hprod : b * a * s ^ 2 = 1 := by rw [hsq, mul_inv_cancel₀ (mul_ne_zero hb0 ha)]
  have hphase (z : ℂ) : ψ (a * (s * z) ^ 2 / 2) = complexStandardCharacter (z ^ 2 / 2) := by
    rw [hb]
    congr 1
    calc
      _ = (b * a * s ^ 2) * (z ^ 2 / 2) := by ring
      _ = _ := by rw [hprod, one_mul]
  have hd : 0 < ‖s‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hs)
  have ht : Tendsto (fun ε : ℝ => ε * ‖s‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [zero_mul] using h0.mul_const (‖s‖ ^ 2)
    · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε
      exact mul_pos hε hd
  let r : ℝ := (addEquivAddHaarChar (complexScalarAddEquiv s hs) : ℝ) * complexReferenceHaarFactor
  refine ⟨r, mul_pos (addEquivAddHaarChar_pos _) complexReferenceHaarFactor_pos, ?_⟩
  have h := (regularizedGaussian_complex_standard_tendsto.comp ht).const_mul
    (addEquivAddHaarChar (complexScalarAddEquiv s hs) : ℂ)
  have hr : (r : ℂ) = (addEquivAddHaarChar (complexScalarAddEquiv s hs) : ℂ) *
      (complexReferenceHaarFactor : ℂ) := by simp only [r, Complex.ofReal_mul]
  rw [hr]
  apply h.congr
  intro ε
  exact (regularizedGaussian_complex_substitution ψ a s hs hphase ε).symm

theorem complex_gaussian_normalization
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z)) (hu : ∀ z, ‖ψ z‖ = 1)
    (hn : ∃ z, ψ z ≠ 1) (a : ℂ) (ha : a ≠ 0) :
    Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian ℂ ψ a) (𝓝[>] (0 : ℝ)) (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral ℂ ψ a)) ∧
      FunctionsMetaplectic.Construction.gaussianIntegral ℂ ψ a ≠ 0 ∧ FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ a = 1 := by
  obtain ⟨r, hr, ht⟩ := complex_gaussian_limit_positive ψ hc hu hn a ha
  have hi : FunctionsMetaplectic.Construction.gaussianIntegral ℂ ψ a = (r : ℂ) := ht.limUnder_eq
  refine ⟨by rwa [hi], ?_, ?_⟩
  · rw [hi]
    exact Complex.ofReal_ne_zero.mpr hr.ne'
  · rw [FunctionsMetaplectic.Construction.gaussianIndex, hi]
    exact Gaussian.Construction.phase_positive_real r hr

end

end OAI.RepresentationTheory.Weil.Local.ArchimedeanTestSpace.Construction
