import OAI.RepresentationTheory.Weil.UnitarySplitting.RealBilinearFourier
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakGaussianNonzero
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylResolutionOperator

/-! # Real Weak Gaussian -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealWeakGaussian.Construction

noncomputable section

/-! Integrability, nonvanishing, and linearity of real weak Gaussian forms. -/

open _root_.MeasureTheory

variable {d : ℕ} (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t))
variable (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure]

include hc hu hn

theorem weakWeylGaussian_integrable_real (μ : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d)) [μ.IsAddHaarMeasure]
    (q : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d → ℝ) (hq : Continuous q) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    Integrable (fun v => ψ (q v) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val v) ν := by
  obtain ⟨Φ, hΦ⟩ := RealWeylCoefficients.Construction.exists_real_weyl_coefficient_schwartz ψ hc hu hn μ f h
  have hi : Integrable Φ ν := Φ.integrable
  have heq : (fun v => ψ (q v) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val v) =
      fun v => ψ (q v) * Φ v := by
    funext v
    rw [hΦ]
  rw [heq]
  apply hi.norm.mono' (((hc.comp hq).mul Φ.continuous).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun v => by
    change ‖ψ (q v) * Φ v‖ ≤ ‖Φ v‖
    rw [norm_mul, hu, one_mul]

theorem weakWeylGaussian_nonzero_real (q : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d → ℝ) (hq : Continuous q) :
    ∃ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d,
      WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure ℝ d) ν q f.val h.val ≠ 0 := by
  obtain ⟨u, hu0⟩ := LocalTest.Construction.exists_test_nonzero_of_real_coordinates (ContinuousAddEquiv.refl (Local.FunctionsMetaplectic.Construction.Position ℝ d))
  let C := WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure ℝ d) u.val u.val
  let φ : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d → ℂ := fun v => ψ (q v) * C v
  have hφc : Continuous φ := (hc.comp hq).mul
    (WeylMatrixCoefficients.Construction.weylMatrixCoefficient_continuous ψ hc hu (Weak.Construction.referencePositionMeasure ℝ d) u u)
  have hφi : Integrable φ ν := weakWeylGaussian_integrable_real ψ hc hu hn ν
    (Weak.Construction.referencePositionMeasure ℝ d) q hq u u
  have hC0 : C 0 ≠ 0 := WeylResolutionOperator.Construction.weylMatrixCoefficient_self_zero_ne_zero RealFourierUnitary.Construction.real_nondiscrete ψ hc hu u hu0
  have hφ0 : φ 0 ≠ 0 := by
    apply mul_ne_zero _ hC0
    intro hz
    have hh := hu (q 0)
    rw [hz, norm_zero] at hh
    exact zero_ne_one hh
  let e : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d ≃L[ℝ] Local.FunctionsMetaplectic.Construction.Position ℝ (d + d) :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (d + d) => ℝ) finSumFinEquiv
  obtain ⟨w, hw⟩ := BilinearFourierInjectivity.Construction.exists_bilinear_fourier_integral_ne_zero e (StandardTransvections.Construction.standardSymplecticBilinear ℝ d)
    (StandardTransvections.Construction.standardSymplecticBilinear_nondegenerate d) ψ hc hu hn ν φ hφi hφc ⟨0, hφ0⟩
  refine ⟨HeisenbergStability.Construction.heisenbergOperator RealFourierUnitary.Construction.real_nondiscrete ψ hc hu w u,
    HeisenbergStability.Construction.heisenbergOperator RealFourierUnitary.Construction.real_nondiscrete ψ hc hu w u, ?_⟩
  have heq : WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure ℝ d) ν q
      (HeisenbergStability.Construction.heisenbergOperator RealFourierUnitary.Construction.real_nondiscrete ψ hc hu w u).val
      (HeisenbergStability.Construction.heisenbergOperator RealFourierUnitary.Construction.real_nondiscrete ψ hc hu w u).val =
        ∫ v, ψ (StandardTransvections.Construction.standardSymplecticBilinear ℝ d v w) * φ v ∂ν := by
    unfold WeakWeylGaussian.Construction.weakWeylGaussian
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => by
      dsimp only
      rw [WeylConjugation.Construction.weylMatrixCoefficient_conjugation RealFourierUnitary.Construction.real_nondiscrete ψ hc hu]
      change ψ (q v) * (ψ (Oscillator.Construction.standardSymplecticPairing d v w) * C v) =
        ψ (Oscillator.Construction.standardSymplecticPairing d v w) * (ψ (q v) * C v)
      ring
  rw [heq]
  exact hw

theorem weakWeylGaussian_add_left_real (q : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d → ℝ) (hq : Continuous q)
    (f₁ f₂ h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure ℝ d) ν q (f₁ + f₂).val h.val =
      WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure ℝ d) ν q f₁.val h.val +
        WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure ℝ d) ν q f₂.val h.val := by
  unfold WeakWeylGaussian.Construction.weakWeylGaussian
  rw [← integral_add
    (weakWeylGaussian_integrable_real ψ hc hu hn ν (Weak.Construction.referencePositionMeasure ℝ d) q hq f₁ h)
    (weakWeylGaussian_integrable_real ψ hc hu hn ν (Weak.Construction.referencePositionMeasure ℝ d) q hq f₂ h)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    dsimp only
    rw [WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner RealFourierUnitary.Construction.real_nondiscrete ψ hc hu, map_add, map_add,
      inner_add_right, WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner RealFourierUnitary.Construction.real_nondiscrete ψ hc hu,
      WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner RealFourierUnitary.Construction.real_nondiscrete ψ hc hu]
    ring

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealWeakGaussian.Construction
