import OAI.RepresentationTheory.Weil.UnitarySplitting.NormGaussianNonzero

/-! # Diagonal Norm Gaussian -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.DiagonalNormGaussian.Construction

noncomputable section

section

/-! Products of the one-dimensional norm Gaussian give the Gaussian
formula for diagonal nondegenerate Hermitian forms. -/

open _root_.MeasureTheory _root_.Topology
open scoped BigOperators NNReal ENNReal

def diagonalNormGaussianCutoff
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [MeasurableSpace E] (μ : Measure E) (ψ : AddChar F ℂ) {d : ℕ}
    (a : Fin d → F) (r : ℝ) : ℂ :=
  ∫ z : Fin d → E, ∏ i, (Metric.closedBall (0 : F) r).indicator
    (fun x => ψ x) (a i * Algebra.norm F (z i)) ∂Measure.pi (fun _ => μ)

theorem diagonalNormGaussianCutoff_eq_prod
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] (ψ : AddChar F ℂ) {d : ℕ}
    (a : Fin d → F) (r : ℝ) :
    diagonalNormGaussianCutoff μ ψ a r = ∏ i, UltraNormGaussian.Construction.normGaussianCutoff μ ψ (a i) r := by
  unfold diagonalNormGaussianCutoff UltraNormGaussian.Construction.normGaussianCutoff
  exact integral_fintype_prod_eq_prod (μ := fun _ : Fin d => μ)
    (fun i : Fin d => fun b : E => (Metric.closedBall (0 : F) r).indicator
      (fun x => ψ x) (a i * Algebra.norm F b))

theorem diagonal_norm_gaussian_formula
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (ψ : AddChar F ℂ) (ω : Fˣ →ₜ* Circle) (Γ : ℂ) (R : ℝ)
    (hformula : ∀ r : ℝ, R ≤ r → ∀ a : Fˣ,
      (FieldModulus.Construction.fieldModulus F a : ℂ) * UltraNormGaussian.Construction.normGaussianCutoff μ ψ (a : F) r = (ω a : ℂ) * Γ)
    {d : ℕ} (a : Fin d → Fˣ) (r : ℝ) (hr : R ≤ r) :
    (FieldModulus.Construction.fieldModulus F (∏ i, a i) : ℂ) * diagonalNormGaussianCutoff μ ψ (fun i => (a i : F)) r =
      (ω (∏ i, a i) : ℂ) * Γ ^ d := by
  rw [diagonalNormGaussianCutoff_eq_prod, map_prod, NNReal.coe_prod, Complex.ofReal_prod,
    ← Finset.prod_mul_distrib]
  simp_rw [hformula r hr]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    map_prod]
  congr 1
  exact (map_prod Circle.coeHom _ _).symm

end

/-! The unit-circle phase of a nonzero Gaussian integral removes all
positive Haar normalization factors. -/

open scoped BigOperators

def gaussianPhase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

theorem gaussianPhase_mul (z w : ℂ) : gaussianPhase (z * w) = gaussianPhase z * gaussianPhase w := by
  unfold gaussianPhase
  rw [norm_mul, Complex.ofReal_mul, mul_div_mul_comm]

theorem gaussianPhase_pow (z : ℂ) (n : ℕ) : gaussianPhase (z ^ n) = gaussianPhase z ^ n := by
  unfold gaussianPhase
  rw [norm_pow, Complex.ofReal_pow, div_pow]

theorem gaussianPhase_positive (r : ℝ) (hr : 0 < r) : gaussianPhase (r : ℂ) = 1 := by
  unfold gaussianPhase
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self (Complex.ofReal_ne_zero.mpr hr.ne')]

theorem gaussianPhase_circle (u : Circle) : gaussianPhase (u : ℂ) = (u : ℂ) := by
  unfold gaussianPhase
  rw [u.norm_coe, Complex.ofReal_one, div_one]

theorem gaussianPhase_norm {z : ℂ} (hz : z ≠ 0) : ‖gaussianPhase z‖ = 1 := by
  unfold gaussianPhase
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr hz)]

def gaussianCircle (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨gaussianPhase z, mem_sphere_zero_iff_norm.mpr (gaussianPhase_norm hz)⟩

theorem positive_weight_gaussian_phase (r : ℝ) (hr : 0 < r) (u : Circle) (z w : ℂ)
    (h : (r : ℂ) * z = (u : ℂ) * w) : gaussianPhase z = (u : ℂ) * gaussianPhase w := by
  have hh := congrArg gaussianPhase h
  rwa [gaussianPhase_mul, gaussianPhase_mul, gaussianPhase_positive r hr,
    gaussianPhase_circle, one_mul] at hh

theorem diagonal_norm_gaussian_phase
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace E] (μ : MeasureTheory.Measure E) [MeasureTheory.SigmaFinite μ]
    (ψ : AddChar F ℂ) (ω : Fˣ →ₜ* Circle) (Γ : ℂ) (R : ℝ)
    (hformula : ∀ r : ℝ, R ≤ r → ∀ a : Fˣ,
      (FieldModulus.Construction.fieldModulus F a : ℂ) * UltraNormGaussian.Construction.normGaussianCutoff μ ψ (a : F) r = (ω a : ℂ) * Γ)
    {d : ℕ} (a : Fin d → Fˣ) (r : ℝ) (hr : R ≤ r) :
    gaussianPhase (diagonalNormGaussianCutoff μ ψ (fun i => (a i : F)) r) =
      (ω (∏ i, a i) : ℂ) * gaussianPhase Γ ^ d := by
  have hpos : 0 < (FieldModulus.Construction.fieldModulus F (∏ i, a i) : ℝ) := FieldModulus.Construction.fieldModulus_pos _
  have hh := positive_weight_gaussian_phase _ hpos (ω (∏ i, a i)) _ (Γ ^ d)
    (diagonal_norm_gaussian_formula μ ψ ω Γ R hformula a r hr)
  rwa [gaussianPhase_pow] at hh

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.DiagonalNormGaussian.Construction
