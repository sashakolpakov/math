import OAI.RepresentationTheory.Weil.UnitarySplitting.DiagonalNormGaussian
import OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanQuadraticCharacter

/-! # Real Gaussian Phase -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealGaussianPhase.Construction

noncomputable section

/-! The phase of the real-place norm Gaussian scales by the specified
quadratic character. -/

theorem gaussianPhase_div (z w : ℂ) : DiagonalNormGaussian.Construction.gaussianPhase (z / w) = DiagonalNormGaussian.Construction.gaussianPhase z / DiagonalNormGaussian.Construction.gaussianPhase w := by
  unfold DiagonalNormGaussian.Construction.gaussianPhase
  rw [norm_div, Complex.ofReal_div, div_div_div_comm]

theorem gaussianPhase_real_ne_zero (a : ℝ) (ha : a ≠ 0) :
    DiagonalNormGaussian.Construction.gaussianPhase (a : ℂ) = if 0 < a then 1 else -1 := by
  unfold DiagonalNormGaussian.Construction.gaussianPhase
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hp : 0 < a
  · rw [ite_eq_left hp, abs_of_pos hp, div_self (Complex.ofReal_ne_zero.mpr ha)]
  · have hn : a < 0 := lt_of_le_of_ne (le_of_not_gt hp) ha
    rw [ite_eq_right hp, abs_of_neg hn, Complex.ofReal_neg, div_neg,
      div_self (Complex.ofReal_ne_zero.mpr ha)]

theorem archimedean_gaussian_phase_scaling
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E] [FiniteDimensional F E]
    (e : ℝ ≃+* F) (k : E ≃+* ℂ)
    (hN : ∀ x : E, e.symm (Algebra.norm F x) = Complex.normSq (k x))
    (hQuadratic : Module.finrank F E = 2)
    (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (z : ℂ) (a : Fˣ) :
    DiagonalNormGaussian.Construction.gaussianPhase (z / (e.symm (a : F) : ℂ)) = (ω a : ℂ) * DiagonalNormGaussian.Construction.gaussianPhase z := by
  have ha : e.symm (a : F) ≠ 0 := (map_ne_zero e.symm).mpr a.ne_zero
  rw [gaussianPhase_div, gaussianPhase_real_ne_zero _ ha]
  by_cases hp : 0 < e.symm (a : F)
  · rw [ite_eq_left hp, (ArchimedeanQuadraticCharacter.Construction.quadraticCharacter_real_positive_iff e k hN ω hω a).mpr hp,
      Circle.coe_one, div_one, one_mul]
  · have hωne : ω a ≠ 1 := fun h => hp ((ArchimedeanQuadraticCharacter.Construction.quadraticCharacter_real_positive_iff e k hN ω hω a).mp h)
    have hs : (ω a : ℂ) ^ 2 = 1 := congrArg (fun u : Circle => (u : ℂ))
      (Characters.Construction.quadraticCharacter_square hQuadratic ω hω a)
    have hm : (ω a : ℂ) = -1 := (sq_eq_one_iff.mp hs).resolve_left (fun h => hωne (Circle.ext h))
    rw [ite_eq_right hp, hm, div_neg, div_one, neg_one_mul]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealGaussianPhase.Construction
