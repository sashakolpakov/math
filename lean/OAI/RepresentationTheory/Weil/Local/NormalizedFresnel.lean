import OAI.RepresentationTheory.Weil.Local.FresnelLimit
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanCover

/-! # Normalized Fresnel -/

namespace OAI.RepresentationTheory.Weil.Local.NormalizedFresnel.Construction

noncomputable section

section

/-! The oscillator Fourier lift with precisely the reference-defined self-dual measure. -/

open _root_.MeasureTheory
open scoped Classical

theorem exists_nonarchimedean_normalized_fourier_oscillator
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) :
    ∃ w : FunctionsMetaplectic.Construction.Oscillator k n ψ, OscillatorProjection.Construction.oscillatorProjection k n ψ w = Generators.Construction.weylSymplectic k n ∧
      ∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n),
        (w.val.2 f).val x = FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val x := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hNondiscrete
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hNondiscrete
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let μ := FunctionsMetaplectic.Construction.positionMeasure k n ψ
  let : (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
    NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hNondiscrete ψ hu hc hn
  let : μ.IsAddHaarMeasure := by dsimp [μ, FunctionsMetaplectic.Construction.positionMeasure]; infer_instance
  obtain ⟨a, T, ha, hT, hunit⟩ :=
    NonarchimedeanFourier.Construction.exists_nonarchimedean_unitary_fourier hNondiscrete n ψ hu hc hn μ
  have hplan (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
      (∫ x, ‖FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x‖ ^ 2 ∂μ) = ∫ x, ‖f.val x‖ ^ 2 ∂μ := by
    obtain ⟨hf, hs⟩ := NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp f.property
    have hF := CompactCharacter.Construction.nonarchimedean_fourier_mem hNondiscrete ψ hu hc hn μ f
    obtain ⟨hFc, hFs⟩ := NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp hF
    have h := NonarchimedeanFourier.Construction.fourierIntegral_norm_sq_of_square ψ hu hc μ
      (hf.continuous.integrable_of_hasCompactSupport hs)
      (hFc.continuous.integrable_of_hasCompactSupport hFs) 1
      (fun x => by simpa only [Complex.ofReal_one, one_mul] using
        NonarchimedeanNormalization.Construction.nonarchimedean_fourier_inversion_selfDual hNondiscrete n ψ hu hc hn f x)
    simpa only [one_mul] using h
  let U := IsUltrametricDist.closedBall_openAddSubgroup (FunctionsMetaplectic.Construction.Position k n) zero_lt_one
  have hU : IsCompact (U : Set (FunctionsMetaplectic.Construction.Position k n)) := isCompact_closedBall 0 1
  let f : FunctionsMetaplectic.Construction.schwartzBruhat k n := ⟨(U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => 1),
    FunctionsMetaplectic.Construction.compact_locallyConstant_mem (CompactCharacter.Construction.subgroup_indicator_locallyConstant U)
      (CompactCharacter.Construction.subgroup_indicator_compactSupport U hU)⟩
  have hE : (∫ x, ‖f.val x‖ ^ 2 ∂μ) = μ.real (U : Set (FunctionsMetaplectic.Construction.Position k n)) := by
    have hv : (fun x => ‖f.val x‖ ^ 2) = (U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ U <;> simp [f, hx]
    rw [hv, integral_indicator_const _ U.isOpen.measurableSet, smul_eq_mul, mul_one]
  have hscale := hunit f
  simp_rw [hT, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, mul_pow] at hscale
  rw [integral_const_mul, hplan, hE] at hscale
  have hsq : a ^ 2 = 1 := mul_right_cancel₀ (NonarchimedeanFourier.Construction.compact_open_subgroup_real_pos μ U hU).ne'
    (hscale.trans (one_mul _).symm)
  have ha1 : a = 1 := (sq_eq_one_iff.mp hsq).resolve_right (by intro h; linarith)
  have hTF (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
      (T f).val x = FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x := by simpa only [ha1, Complex.ofReal_one, one_mul] using hT f x
  have hunitref (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) : FunctionsMetaplectic.Construction.l2Energy k n (T f) = FunctionsMetaplectic.Construction.l2Energy k n f := by
    let ν : Measure (FunctionsMetaplectic.Construction.Position k n) := Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k))
    have h := Measure.isAddLeftInvariant_eq_smul_of_regular ν μ
    change (∫ x, ‖(T f).val x‖ ^ 2 ∂ν) = ∫ x, ‖f.val x‖ ^ 2 ∂ν
    rw [h, integral_smul_nnreal_measure, integral_smul_nnreal_measure, hunit]
  refine ⟨⟨(Generators.Construction.weylSymplectic k n, T), ⟨hunitref, ?_⟩⟩, rfl, hTF⟩
  exact NonarchimedeanFourier.Construction.scalar_fourier_intertwines hNondiscrete ψ hu hc μ 1 T
    (fun f x => by rw [one_mul]; exact hTF f x)

end

section

/-! The Fourier–quadratic operator identity with its exact Gaussian phase. -/

open _root_.MeasureTheory
open scoped Classical

theorem standardQuadratic_complete_square
    {k : Type} [Field k] [CharZero k] {n : ℕ} (x y : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic (1 : Matrix (Fin n) (Fin n) k) (y + x) - FunctionsMetaplectic.Construction.dot x (y + x) =
      FunctionsMetaplectic.Construction.quadratic 1 y - FunctionsMetaplectic.Construction.quadratic 1 x := by
  simp only [FresnelLimit.Construction.quadratic_one_sum, FunctionsMetaplectic.Construction.dot, Pi.add_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h2 : (2 : k) ≠ 0 := by norm_num
  field_simp
  ring

theorem fourierIntegral_modulation
    {k : Type} [Field k] [MeasurableSpace k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) (f : FunctionsMetaplectic.Construction.Position k n → ℂ)
    (x y : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ μ (fun z => f z * ψ (-FunctionsMetaplectic.Construction.dot x z)) y =
      FunctionsMetaplectic.Construction.fourierIntegral ψ μ f (y + x) := by
  unfold FunctionsMetaplectic.Construction.fourierIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    dsimp only
    rw [mul_assoc, ← ψ.map_add_eq_mul]
    congr 2
    simp only [FunctionsMetaplectic.Construction.dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring

theorem fourier_quadratic_shift
    {k : Type} [NormedField k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (f : FunctionsMetaplectic.Construction.Position k n → ℂ) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.quadraticOperator ψ 1 (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f)) x =
      ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) * ∫ y, FunctionsMetaplectic.Construction.fourierIntegral ψ μ (fun z => f z * ψ (-FunctionsMetaplectic.Construction.dot x z)) y *
        ψ (FunctionsMetaplectic.Construction.quadratic 1 y) ∂μ := by
  rw [FunctionsMetaplectic.Construction.fourierIntegral, ← integral_add_right_eq_self _ x, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [FunctionsMetaplectic.Construction.quadraticOperator_apply, fourierIntegral_modulation]
    have hp : ψ (FunctionsMetaplectic.Construction.quadratic 1 (y + x)) * ψ (-FunctionsMetaplectic.Construction.dot x (y + x)) =
        ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) * ψ (FunctionsMetaplectic.Construction.quadratic 1 y) := by
      rw [← ψ.map_add_eq_mul, ← ψ.map_add_eq_mul]
      congr 1
      simpa only [sub_eq_add_neg, add_comm] using standardQuadratic_complete_square x y
    calc
      _ = (ψ (FunctionsMetaplectic.Construction.quadratic 1 (y + x)) * ψ (-FunctionsMetaplectic.Construction.dot x (y + x))) * FunctionsMetaplectic.Construction.fourierIntegral ψ μ f (y + x) := by ring
      _ = _ := by rw [hp]; ring

theorem modulated_quadratic_integral
    {k : Type} [Field k] [MeasurableSpace k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) (f : FunctionsMetaplectic.Construction.Position k n → ℂ)
    (x : FunctionsMetaplectic.Construction.Position k n) :
    (∫ y, (f y * ψ (-FunctionsMetaplectic.Construction.dot x y)) * ψ (-FunctionsMetaplectic.Construction.quadratic 1 y) ∂μ) =
      FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.quadraticOperator ψ (-1) f) x := by
  unfold FunctionsMetaplectic.Construction.fourierIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change (f y * ψ (-FunctionsMetaplectic.Construction.dot x y)) * ψ (-FunctionsMetaplectic.Construction.quadratic 1 y) =
      (ψ (FunctionsMetaplectic.Construction.quadratic (-1) y) * f y) * ψ (-FunctionsMetaplectic.Construction.dot x y)
    rw [FunctionsMetaplectic.Construction.quadratic_neg]
    ring

theorem nonarchimedean_modulation_mem
    {k : Type} [NormedField k] [NonarchimedeanAddGroup k] {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    (fun z => f.val z * ψ (-FunctionsMetaplectic.Construction.dot x z)) ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n := by
  obtain ⟨hf, hs⟩ := NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp f.property
  apply FunctionsMetaplectic.Construction.compact_locallyConstant_mem
  · exact hf.mul ((NonarchimedeanTestSpace.Construction.nonarchimedean_character_locallyConstant ψ hu hc).comp_continuous
      (by unfold FunctionsMetaplectic.Construction.dot; fun_prop))
  · exact hs.mul_right

theorem nonarchimedean_fourier_quadratic_fourier
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ)
      (FunctionsMetaplectic.Construction.quadraticOperator ψ 1 (FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val)) x =
      FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n * ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) *
        FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) (FunctionsMetaplectic.Construction.quadraticOperator ψ (-1) f.val) x := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let : (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
    NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hNondiscrete ψ hu hc hn
  let μ := FunctionsMetaplectic.Construction.positionMeasure k n ψ
  let : μ.IsAddHaarMeasure := by dsimp [μ, FunctionsMetaplectic.Construction.positionMeasure]; infer_instance
  let g : FunctionsMetaplectic.Construction.schwartzBruhat k n := ⟨fun z => f.val z * ψ (-FunctionsMetaplectic.Construction.dot x z),
    nonarchimedean_modulation_mem ψ hu hc f x⟩
  have hpair := FresnelLimit.Construction.nonarchimedean_fresnel_pairing hNondiscrete ψ hu hc hn g
  calc
    _ = ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) * ∫ y, FunctionsMetaplectic.Construction.fourierIntegral ψ μ g.val y * ψ (FunctionsMetaplectic.Construction.quadratic 1 y) ∂μ :=
      fourier_quadratic_shift ψ μ f.val x
    _ = ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) * (FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n * ∫ y, g.val y * ψ (-FunctionsMetaplectic.Construction.quadratic 1 y) ∂μ) :=
      congrArg (fun z : ℂ => ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) * z) hpair
    _ = ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) * (FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n *
        FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.quadraticOperator ψ (-1) f.val) x) :=
      congrArg (fun z : ℂ => ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) * (FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n * z))
        (modulated_quadratic_integral ψ μ f.val x)
    _ = _ := by ring

end

/-! The specified Gaussian-normalized Weyl operator belongs to the intrinsic bare cover. -/

open _root_.MeasureTheory
open scoped Classical

theorem weyl_lower_unipotent_factorization {k : Type} [Field k] (n : ℕ) :
    Generators.Construction.quadraticSymplectic (k := k) ⟨-1, Matrix.isSymm_one.neg⟩ *
      GenerationSymplectic.Construction.upperSymplectic ⟨1, Matrix.isSymm_one⟩ *
      Generators.Construction.quadraticSymplectic ⟨-1, Matrix.isSymm_one.neg⟩ = Generators.Construction.weylSymplectic k n := by
  apply Subtype.ext
  change (Generators.Construction.quadraticSymplectic (k := k) ⟨-1, Matrix.isSymm_one.neg⟩).val *
      (GenerationSymplectic.Construction.upperSymplectic ⟨1, Matrix.isSymm_one⟩).val *
      (Generators.Construction.quadraticSymplectic ⟨-1, Matrix.isSymm_one.neg⟩).val = (Generators.Construction.weylSymplectic k n).val
  simp [Generators.Construction.weylSymplectic, GenerationSymplectic.Construction.upperSymplectic, Generators.Construction.quadraticSymplectic, Matrix.fromBlocks_multiply]

theorem linearEquiv_weyl_word
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T P : E ≃ₗ[ℂ] E) (c : ℂ) (hc : c ≠ 0)
    (h : ∀ f, T (P (T f)) = c • P.symm (T (P.symm f))) (f : E) :
    P.symm (T.symm (P.symm (T (P.symm f)))) = c⁻¹ • T f := by
  apply P.injective
  apply T.injective
  rw [P.apply_symm_apply, T.apply_symm_apply, map_smul, map_smul, h,
    smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem nonarchimedean_fourier_quadratic_relation
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (T : FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n)
    (hT : ∀ f x, (T f).val x = FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val x)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    let P := QuadraticIntertwiner.Construction.testQuadratic ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) 1
    T (P (T f)) = FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n • P.symm (T (P.symm f)) := by
  let P := QuadraticIntertwiner.Construction.testQuadratic ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) (1 : Matrix (Fin n) (Fin n) k)
  have hTf (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) : (T f).val = FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val := funext (hT f)
  have hP (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) : (P f).val = FunctionsMetaplectic.Construction.quadraticOperator ψ 1 f.val := rfl
  have hN (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) : (P.symm f).val = FunctionsMetaplectic.Construction.quadraticOperator ψ (-1) f.val := rfl
  change T (P (T f)) = FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n • P.symm (T (P.symm f))
  apply Subtype.ext
  change (T (P (T f))).val = (FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n) • (P.symm (T (P.symm f))).val
  rw [hTf, hP, hTf, hN, hTf, hN]
  funext x
  change _ = FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n *
    (ψ (FunctionsMetaplectic.Construction.quadratic (-1) x) * FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) (FunctionsMetaplectic.Construction.quadraticOperator ψ (-1) f.val) x)
  rw [FunctionsMetaplectic.Construction.quadratic_neg, ← mul_assoc]
  exact nonarchimedean_fourier_quadratic_fourier hNondiscrete ψ hu hc hn f x

theorem exists_nonarchimedean_weyl_metaplectic
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) :
    ∃ w : FunctionsMetaplectic.Construction.Metaplectic k n ψ, FunctionsMetaplectic.Construction.metaplecticProjection k n ψ w = Generators.Construction.weylSymplectic k n ∧
      ∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n),
        (FunctionsMetaplectic.Construction.weilRepresentation k n ψ w f).val x =
          (FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n)⁻¹ * FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val x := by
  obtain ⟨w, hw, hT⟩ := exists_nonarchimedean_normalized_fourier_oscillator hNondiscrete n ψ hu hc hn
  let u := NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hu hc
    (⟨-1, Matrix.isSymm_one.neg⟩ : FunctionsMetaplectic.Construction.SymmetricMatrix k n)
  have hconj : w⁻¹ * u.val * w ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ := by
    have h := (inferInstance : (FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ).Normal).conj_mem u.val u.property w⁻¹
    simpa only [inv_inv] using h
  let v : FunctionsMetaplectic.Construction.Metaplectic k n ψ := ⟨u.val * (w⁻¹ * u.val * w) * u.val,
    (FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ).mul_mem
      ((FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ).mul_mem u.property hconj) u.property⟩
  have huProj : OscillatorProjection.Construction.oscillatorProjection k n ψ u.val = Generators.Construction.quadraticSymplectic ⟨-1, Matrix.isSymm_one.neg⟩ := rfl
  have hupper : OscillatorProjection.Construction.oscillatorProjection k n ψ (w⁻¹ * u.val * w) = GenerationSymplectic.Construction.upperSymplectic ⟨1, Matrix.isSymm_one⟩ := by
    rw [map_mul, map_mul, map_inv, hw, huProj]
    exact (OscillatorProjection.Construction.upper_quadratic_conjugation k n ⟨1, Matrix.isSymm_one⟩).symm
  refine ⟨v, ?_, ?_⟩
  · change OscillatorProjection.Construction.oscillatorProjection k n ψ (u.val * (w⁻¹ * u.val * w) * u.val) = _
    rw [map_mul, map_mul, huProj, hupper]
    exact weyl_lower_unipotent_factorization n
  · let P := QuadraticIntertwiner.Construction.testQuadratic ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) (1 : Matrix (Fin n) (Fin n) k)
    have hN : u.val.val.2 = P.symm := by
      apply LinearEquiv.ext
      intro f
      rfl
    have hγ : FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n ≠ 0 := pow_ne_zero _ (by
      have h := FunctionsMetaplectic.Construction.gaussianIndex_norm k ψ 1
        (GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hNondiscrete ψ hu hc hn 1 one_ne_zero).2
      intro hz
      rw [hz, norm_zero] at h
      exact zero_ne_one h)
    have hrel := nonarchimedean_fourier_quadratic_relation hNondiscrete ψ hu hc hn w.val.2 hT
    have hword := linearEquiv_weyl_word w.val.2 P (FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n) hγ hrel
    intro f x
    have hop : FunctionsMetaplectic.Construction.weilRepresentation k n ψ v f =
        P.symm (w.val.2.symm (P.symm (w.val.2 (P.symm f)))) := by
      change ((u.val.val.2 * ((w.val.2)⁻¹ * u.val.val.2 * w.val.2)) * u.val.val.2) f = _
      rw [hN]
      rfl
    rw [hop, hword]
    change (FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n)⁻¹ * (w.val.2 f).val x = _
    rw [hT]

end

end OAI.RepresentationTheory.Weil.Local.NormalizedFresnel.Construction
