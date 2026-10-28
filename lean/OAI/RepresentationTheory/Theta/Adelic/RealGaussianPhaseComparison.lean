import OAI.RepresentationTheory.Weil.UnitarySplitting.ComplexGaussianFourier
import OAI.RepresentationTheory.Theta.Adelic.NormalizedNormGaussian

/-! # Real Gaussian Phase Comparison -/

namespace OAI.RepresentationTheory.Theta.Adelic.RealGaussianPhaseComparison

noncomputable section

/-! The actual complex norm Gaussian phase equals the two real scalar
Gaussian phases used by the native normalization. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.ComplexGaussianFourier.Construction

theorem negative_of_nonsquare (d : ℝ) (hns : ¬ IsSquare d) : d < 0 := by
  apply lt_of_not_ge
  intro hd
  apply hns
  exact ⟨Real.sqrt d, by rw [← pow_two, Real.sq_sqrt hd]⟩

theorem complex_norm_phase_eq (d : ℝ) (hd : d < 0) (c : ℝ) (hc : c ≠ 0) :
    Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase (Weil.UnitarySplitting.ComplexGaussianFourier.Construction.complexNormGaussianValue (2 * Real.pi * c)) =
      Weil.AdelicSplitting.Normalization.Construction.quadraticWeilConstant ℝ (Weil.Local.Gaussian.Construction.realCharacter c) d := by
  have hvalue : Weil.UnitarySplitting.ComplexGaussianFourier.Construction.complexNormGaussianValue (2 * Real.pi * c) =
      ((1 / 2 : ℝ) : ℂ) * (Complex.I / (c : ℂ)) := by
    unfold Weil.UnitarySplitting.ComplexGaussianFourier.Construction.complexNormGaussianValue
    push_cast
    field_simp [Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr hc,
      Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring_nf
    simp [Complex.I_sq]
  rw [hvalue, Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase_mul, Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase_positive (1 / 2 : ℝ) (by norm_num), one_mul]
  rw [Weil.AdelicSplitting.Normalization.Construction.quadraticWeilConstant, Weil.Local.RealLevi.Construction.gaussianIndex_real_positive_argument c hc (-d) (neg_pos.mpr hd),
    ← pow_two, Weil.Local.Gaussian.Construction.gaussianIndex_real_eq c 1 hc one_ne_zero, Weil.Local.Gaussian.Construction.phase_pow]
  simp only [Complex.ofReal_one, mul_one]
  have hs : ((Complex.I / (c : ℂ)) ^ (1 / 2 : ℂ)) ^ (2 : ℕ) = Complex.I / (c : ℂ) := by
    simp [one_div]
  rw [hs]
  rfl

end

end OAI.RepresentationTheory.Theta.Adelic.RealGaussianPhaseComparison
