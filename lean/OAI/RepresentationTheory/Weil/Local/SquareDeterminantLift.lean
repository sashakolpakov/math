import OAI.RepresentationTheory.Weil.Local.ComplexLevi
import OAI.RepresentationTheory.Weil.Local.GaussianSquareClasses
import OAI.RepresentationTheory.Weil.Local.RealWeyl

/-! # Square Determinant Lift -/

namespace OAI.RepresentationTheory.Weil.Local.SquareDeterminantLift.Construction

noncomputable section

/-! Exact bare Levi lifts for square determinants. -/

open _root_.MeasureTheory Filter _root_.Matrix
open scoped _root_.Topology Classical

theorem gaussianIndex_square_mul_of_limit
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (ψ : AddChar k ℂ) (a : k) (b : kˣ)
    (hlim : Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ a) (𝓝[>] (0 : ℝ)) (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral k ψ a))) :
    FunctionsMetaplectic.Construction.gaussianIndex k ψ (a * b.val ^ 2) = FunctionsMetaplectic.Construction.gaussianIndex k ψ a := by
  have hscaled := (hlim.comp
    (GaussianSquareClasses.Construction.positive_division_tendsto_zero_right (‖b.val‖ ^ 2) (sq_pos_of_pos (norm_pos_iff.mpr b.ne_zero)))).const_smul
      ((FunctionsMetaplectic.Construction.localModulus k b)⁻¹ : ℝ)
  have hresult : Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ (a * b.val ^ 2)) (𝓝[>] (0 : ℝ))
      (𝓝 (((FunctionsMetaplectic.Construction.localModulus k b)⁻¹ : ℝ) • FunctionsMetaplectic.Construction.gaussianIntegral k ψ a)) := by
    simpa only [Function.comp_def, ← GaussianSquareClasses.Construction.regularizedGaussian_square_mul ψ a b] using hscaled
  have hG : FunctionsMetaplectic.Construction.gaussianIntegral k ψ (a * b.val ^ 2) =
      ((FunctionsMetaplectic.Construction.localModulus k b)⁻¹ : ℝ) • FunctionsMetaplectic.Construction.gaussianIntegral k ψ a := hresult.limUnder_eq
  rw [FunctionsMetaplectic.Construction.gaussianIndex, hG, Complex.real_smul,
    Gaussian.Construction.phase_positive_mul ((FunctionsMetaplectic.Construction.localModulus k b)⁻¹) (inv_pos.mpr (FunctionsMetaplectic.Construction.localModulus_pos k b))]
  rfl

theorem coordinateDiagonal_square
    {k : Type} [Field k] {n : ℕ} (i : Fin n) (b : kˣ) :
    SpecialLinearCommutators.Construction.coordinateDiagonal i b * SpecialLinearCommutators.Construction.coordinateDiagonal i b = SpecialLinearCommutators.Construction.coordinateDiagonal i (b ^ 2) := by
  apply Units.ext
  change diagonal (fun j => if j = i then b.val else 1) * diagonal (fun j => if j = i then b.val else 1) =
    diagonal (fun j => if j = i then b.val ^ 2 else 1)
  rw [diagonal_mul_diagonal]
  congr 1
  funext j
  split_ifs
  · exact (pow_two b.val).symm
  · exact one_mul 1

theorem linearOscillator_mem_of_square_det
    {k : Type} [NormedField k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (hn : 0 < n) (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure]
    (w : FunctionsMetaplectic.Construction.Oscillator k n ψ) (hw : OscillatorProjection.Construction.oscillatorProjection k n ψ w = Generators.Construction.weylSymplectic k n)
    (hT : ∀ f x, (w.val.2 f).val x = FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f.val x)
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (b : kˣ) (hb : b ^ 2 = FunctionsMetaplectic.Construction.determinantUnit k A) :
    LinearIntertwiner.Construction.linearOscillator ψ A ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ := by
  let i : Fin n := ⟨0, hn⟩
  let D := SpecialLinearCommutators.Construction.coordinateDiagonal i (b ^ 2)
  have hD : LinearIntertwiner.Construction.linearOscillator ψ D ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ := by
    rw [show D = SpecialLinearCommutators.Construction.coordinateDiagonal i b * SpecialLinearCommutators.Construction.coordinateDiagonal i b from (coordinateDiagonal_square i b).symm]
    exact SymmetricSquareLift.Construction.linearOscillator_symmetric_square_mem ψ μ w hw hT (SpecialLinearCommutators.Construction.coordinateDiagonal i b) (isSymm_diagonal _)
  let S := A * D⁻¹
  have hS : S.val.det = 1 := by
    change (FunctionsMetaplectic.Construction.determinantUnit k (A * D⁻¹)).val = 1
    rw [LinearOscillatorHom.Construction.determinantUnit_mul, FourierLinearSubstitution.Construction.determinantUnit_inv]
    have hd : FunctionsMetaplectic.Construction.determinantUnit k D = FunctionsMetaplectic.Construction.determinantUnit k A := (ComplexLevi.Construction.coordinateDiagonal_determinant i (b ^ 2)).trans hb
    rw [hd, mul_inv_cancel]
    rfl
  have h := (FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ).mul_mem (SpecialLinearCommutators.Construction.linearOscillator_mem_of_det_one ψ S hS) hD
  rw [← LinearOscillatorHom.Construction.linearOscillator_mul] at h
  simpa only [S, mul_assoc, inv_mul_cancel, mul_one] using h

theorem exists_square_det_levi_metaplectic
    {k : Type} [NormedField k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (hn : 0 < n) (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure]
    (w : FunctionsMetaplectic.Construction.Oscillator k n ψ) (hw : OscillatorProjection.Construction.oscillatorProjection k n ψ w = Generators.Construction.weylSymplectic k n)
    (hT : ∀ f x, (w.val.2 f).val x = FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f.val x)
    (hlim : Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ 1) (𝓝[>] (0 : ℝ)) (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral k ψ 1)))
    (hG : FunctionsMetaplectic.Construction.gaussianIntegral k ψ 1 ≠ 0)
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (b : kˣ) (hb : b ^ 2 = FunctionsMetaplectic.Construction.determinantUnit k A) :
    ∃ m : FunctionsMetaplectic.Construction.Metaplectic k n ψ, FunctionsMetaplectic.Construction.metaplecticProjection k n ψ m = Generators.Construction.leviSymplectic A ∧
      ∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n),
        (FunctionsMetaplectic.Construction.weilRepresentation k n ψ m f).val x =
          (FunctionsMetaplectic.Construction.gaussianIndex k ψ (FunctionsMetaplectic.Construction.determinantUnit k A) / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1) *
            ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A)))⁻¹ : ℂ) * f.val (A⁻¹.val *ᵥ x) := by
  let m : FunctionsMetaplectic.Construction.Metaplectic k n ψ := ⟨LinearIntertwiner.Construction.linearOscillator ψ A, linearOscillator_mem_of_square_det hn ψ μ w hw hT A b hb⟩
  refine ⟨m, rfl, fun f x => ?_⟩
  have hγ : FunctionsMetaplectic.Construction.gaussianIndex k ψ (FunctionsMetaplectic.Construction.determinantUnit k A) = FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 := by
    rw [← hb]
    simpa only [one_mul, Units.val_pow_eq_pow_val] using gaussianIndex_square_mul_of_limit ψ 1 b hlim
  have hγ0 : FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ≠ 0 := by
    intro h
    have hnorm := FunctionsMetaplectic.Construction.gaussianIndex_norm k ψ 1 hG
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  rw [hγ, div_self hγ0, one_mul]
  exact LinearIntertwiner.Construction.linearOscillator_apply ψ A f x

theorem exists_real_positive_det_levi_metaplectic
    {n : ℕ} (hn : 0 < n) (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hψ : ∃ t, ψ t ≠ 1)
    (A : FunctionsMetaplectic.Construction.GeneralLinear ℝ n) (hA : 0 < A.val.det) :
    ∃ m : FunctionsMetaplectic.Construction.Metaplectic ℝ n ψ, FunctionsMetaplectic.Construction.metaplecticProjection ℝ n ψ m = Generators.Construction.leviSymplectic A ∧
      ∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n),
        (FunctionsMetaplectic.Construction.weilRepresentation ℝ n ψ m f).val x =
          (FunctionsMetaplectic.Construction.gaussianIndex ℝ ψ (FunctionsMetaplectic.Construction.determinantUnit ℝ A) / FunctionsMetaplectic.Construction.gaussianIndex ℝ ψ 1) *
            ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus ℝ (FunctionsMetaplectic.Construction.determinantUnit ℝ A)))⁻¹ : ℂ) * f.val (A⁻¹.val *ᵥ x) := by
  obtain ⟨c, hc0, rfl⟩ := RealCharacters.Construction.continuous_nontrivial_unitary_real_character ψ hc hu hψ
  let μ := FunctionsMetaplectic.Construction.selfDualMeasure ℝ (Gaussian.Construction.realCharacter c)
  let : μ.IsAddHaarMeasure := (RealNormalization.Construction.real_analytic_normalization (Gaussian.Construction.realCharacter c) hc hu hψ n).2.1
  let b : ℝˣ := Units.mk0 (Real.sqrt A.val.det) (Real.sqrt_pos.mpr hA).ne'
  have hb : b ^ 2 = FunctionsMetaplectic.Construction.determinantUnit ℝ A := by
    apply Units.ext
    exact Real.sq_sqrt hA.le
  have hG := (RealNormalization.Construction.real_analytic_normalization (Gaussian.Construction.realCharacter c) hc hu hψ n).2.2.1 1 one_ne_zero
  exact exists_square_det_levi_metaplectic hn (Gaussian.Construction.realCharacter c) μ (RealFourierFamily.Construction.realFourierOscillatorFamily n c hc0)
    rfl (RealFourierFamily.Construction.realNormalizedFourier_apply c hc0) hG.1 hG.2.1 A b hb

theorem exists_nonarchimedean_square_det_levi_metaplectic
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ} (hn : 0 < n)
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hψ : ∃ t, ψ t ≠ 1)
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (b : kˣ) (hb : b ^ 2 = FunctionsMetaplectic.Construction.determinantUnit k A) :
    ∃ m : FunctionsMetaplectic.Construction.Metaplectic k n ψ, FunctionsMetaplectic.Construction.metaplecticProjection k n ψ m = Generators.Construction.leviSymplectic A ∧
      ∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n),
        (FunctionsMetaplectic.Construction.weilRepresentation k n ψ m f).val x =
          (FunctionsMetaplectic.Construction.gaussianIndex k ψ (FunctionsMetaplectic.Construction.determinantUnit k A) / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1) *
            ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A)))⁻¹ : ℂ) * f.val (A⁻¹.val *ᵥ x) := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let μ := FunctionsMetaplectic.Construction.selfDualMeasure k ψ
  let : μ.IsAddHaarMeasure := NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hNondiscrete ψ hu hc hψ
  obtain ⟨w, hw, hT⟩ := NormalizedFresnel.Construction.exists_nonarchimedean_normalized_fourier_oscillator hNondiscrete n ψ hu hc hψ
  have hG := GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hNondiscrete ψ hu hc hψ 1 one_ne_zero
  exact exists_square_det_levi_metaplectic hn ψ μ w hw hT hG.1 hG.2 A b hb

end

end OAI.RepresentationTheory.Weil.Local.SquareDeterminantLift.Construction
