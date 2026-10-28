import OAI.RepresentationTheory.Weil.Local.GeneralQuadraticAlgebra
import OAI.RepresentationTheory.Weil.Local.GeneralGaussianCoefficient
import OAI.RepresentationTheory.Weil.Local.NormalizedFresnel

/-! # General Fresnel Operator -/

namespace OAI.RepresentationTheory.Weil.Local.GeneralFresnelOperator.Construction

noncomputable section

section

/-! Fourier–quadratic composition for arbitrary nonsingular symmetric coefficients. -/

open _root_.Matrix _root_.MeasureTheory

theorem general_fourier_quadratic_shift
    {k : Type} [NormedField k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (M : FunctionsMetaplectic.Construction.GeneralLinear k n) (hM : M.val.IsSymm) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.quadraticOperator ψ M.val (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f)) x =
      ψ (-FunctionsMetaplectic.Construction.quadratic M⁻¹.val x) * ∫ y,
        FunctionsMetaplectic.Construction.fourierIntegral ψ μ (fun z => f z * ψ (-FunctionsMetaplectic.Construction.dot (M⁻¹.val *ᵥ x) z)) y *
          ψ (FunctionsMetaplectic.Construction.quadratic M.val y) ∂μ := by
  rw [FunctionsMetaplectic.Construction.fourierIntegral, ← integral_add_right_eq_self _ (M⁻¹.val *ᵥ x), ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [FunctionsMetaplectic.Construction.quadraticOperator_apply, NormalizedFresnel.Construction.fourierIntegral_modulation]
    have hp : ψ (FunctionsMetaplectic.Construction.quadratic M.val (y + M⁻¹.val *ᵥ x)) *
        ψ (-FunctionsMetaplectic.Construction.dot x (y + M⁻¹.val *ᵥ x)) =
        ψ (-FunctionsMetaplectic.Construction.quadratic M⁻¹.val x) *
          ψ (FunctionsMetaplectic.Construction.quadratic M.val y) := by
      rw [← ψ.map_add_eq_mul, ← ψ.map_add_eq_mul]
      congr 1
      simpa only [sub_eq_add_neg, add_comm] using GeneralQuadraticAlgebra.Construction.general_quadratic_complete_square M hM x y
    calc
      _ = (ψ (FunctionsMetaplectic.Construction.quadratic M.val (y + M⁻¹.val *ᵥ x)) *
          ψ (-FunctionsMetaplectic.Construction.dot x (y + M⁻¹.val *ᵥ x))) *
            FunctionsMetaplectic.Construction.fourierIntegral ψ μ f (y + M⁻¹.val *ᵥ x) := by ring
      _ = _ := by rw [hp]; ring

theorem nonarchimedean_general_fourier_quadratic_fourier
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (M : FunctionsMetaplectic.Construction.GeneralLinear k n) (hM : M.val.IsSymm) (c : ℂ)
    (hpair : ∀ g : FunctionsMetaplectic.Construction.schwartzBruhat k n,
      (∫ y, FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) g.val y * ψ (FunctionsMetaplectic.Construction.quadratic M.val y)
        ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ) =
        c * ∫ y, g.val y * ψ (-FunctionsMetaplectic.Construction.quadratic M⁻¹.val y) ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ)
      (FunctionsMetaplectic.Construction.quadraticOperator ψ M.val
        (FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val)) x =
      c * ψ (-FunctionsMetaplectic.Construction.quadratic M⁻¹.val x) *
        FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ)
          (FunctionsMetaplectic.Construction.quadraticOperator ψ (-M⁻¹.val) f.val)
            (M⁻¹.val *ᵥ x) := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let : (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
    NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hNondiscrete ψ hu hc hn
  let μ := FunctionsMetaplectic.Construction.positionMeasure k n ψ
  let : μ.IsAddHaarMeasure := by dsimp [μ, FunctionsMetaplectic.Construction.positionMeasure]; infer_instance
  let g : FunctionsMetaplectic.Construction.schwartzBruhat k n := ⟨fun z => f.val z * ψ (-FunctionsMetaplectic.Construction.dot (M⁻¹.val *ᵥ x) z),
    NormalizedFresnel.Construction.nonarchimedean_modulation_mem ψ hu hc f (M⁻¹.val *ᵥ x)⟩
  have hpairg := hpair g
  have hmod : (∫ y, g.val y * ψ (-FunctionsMetaplectic.Construction.quadratic M⁻¹.val y) ∂μ) =
      FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.quadraticOperator ψ (-M⁻¹.val) f.val)
        (M⁻¹.val *ᵥ x) := by
    unfold FunctionsMetaplectic.Construction.fourierIntegral
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      change (f.val y * ψ (-FunctionsMetaplectic.Construction.dot (M⁻¹.val *ᵥ x) y)) *
        ψ (-FunctionsMetaplectic.Construction.quadratic M⁻¹.val y) =
        (ψ (FunctionsMetaplectic.Construction.quadratic (-M⁻¹.val) y) * f.val y) *
          ψ (-FunctionsMetaplectic.Construction.dot (M⁻¹.val *ᵥ x) y)
      rw [FunctionsMetaplectic.Construction.quadratic_neg]
      ring
  rw [general_fourier_quadratic_shift ψ μ M hM, hpairg, hmod]
  ring

end

/-! The exact normalized general Fourier–quadratic relation. -/

open _root_.Matrix _root_.MeasureTheory

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k]
  [NonarchimedeanAddGroup k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
  [SecondCountableTopology k]
  (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
  (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
  (hns : ¬ ∃ t : k, t ^ 2 = -1)

theorem exists_nonarchimedean_general_fourier_relation {n : ℕ}
    (M : FunctionsMetaplectic.Construction.GeneralLinear k n) (hM : M.val.IsSymm)
    (F : FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n)
    (hF : ∀ f x, (F f).val x = FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val x) :
    ∃ Γ : ℂ,
      Γ ^ 2 = FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ (2 * n) *
        (GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns (FunctionsMetaplectic.Construction.determinantUnit k M)).val ∧
      ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n,
        F (QuadraticIntertwiner.Construction.testQuadratic ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) M.val (F f)) =
          Γ • QuadraticIntertwiner.Construction.testQuadratic ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) (-M⁻¹.val)
            ((LinearIntertwiner.Construction.linearOscillator ψ M).val.2
              (F (QuadraticIntertwiner.Construction.testQuadratic ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) (-M⁻¹.val) f))) := by
  obtain ⟨c, hc2, hpair⟩ := GeneralGaussianCoefficient.Construction.exists_nonarchimedean_general_fresnel_coefficient hnd ψ hu hc hn hns M hM
  let d := FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k M)
  have hd : 0 < d := FunctionsMetaplectic.Construction.localModulus_pos k _
  have hs : (Real.sqrt d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hd).ne'
  refine ⟨(Real.sqrt d : ℂ) * c, ?_, ?_⟩
  · rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt hd.le, hc2]
    have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
    change (d : ℂ) * (_ / (d : ℂ)) = _
    field_simp
  · intro f
    have hFval (g : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
        (F g).val = FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) g.val := funext (hF g)
    apply Subtype.ext
    rw [hFval, QuadraticIntertwiner.Construction.testQuadratic_val, hFval]
    funext x
    change _ = ((Real.sqrt d : ℂ) * c) *
      (ψ (FunctionsMetaplectic.Construction.quadratic (-M⁻¹.val) x) *
        ((LinearIntertwiner.Construction.linearOscillator ψ M).val.2
          (F (QuadraticIntertwiner.Construction.testQuadratic ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) (-M⁻¹.val) f))).val x)
    rw [nonarchimedean_general_fourier_quadratic_fourier hnd ψ hu hc hn M hM c hpair,
      LinearIntertwiner.Construction.linearOscillator_apply, hFval, QuadraticIntertwiner.Construction.testQuadratic_val, FunctionsMetaplectic.Construction.quadratic_neg]
    change _ = ((Real.sqrt d : ℂ) * c) * (_ * (((Real.sqrt d)⁻¹ : ℂ) * _))
    field_simp

end

end OAI.RepresentationTheory.Weil.Local.GeneralFresnelOperator.Construction
