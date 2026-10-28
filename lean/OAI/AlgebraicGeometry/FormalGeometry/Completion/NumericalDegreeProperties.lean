import OAI.AlgebraicGeometry.FormalGeometry.Completion.PicardNumericalDegree

/-! # Numerical Degree Properties -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.NumericalDegreeProperties

noncomputable section

/-! The actual numerical degree is nonnegative on generated line bundles
and becomes integral after one fixed factorial normalization. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Polynomial

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {r : ℕ} {X : Scheme.{u}}
  (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)) [IsClosedImmersion f]

theorem closedProjectiveHilbertPolynomial_eventually_integer
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (j : Fin (r + 1)) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∃ z : ℤ, (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f M j).eval (n : ℚ) = z := by
  obtain ⟨b, hb⟩ := Projective.Numerics.Construction.projectiveHilbertPolynomial_spec (ClosedHilbertNumerics.Construction.coherentClosedDirectImage f M) j
  refine ⟨b, fun n hn => ?_⟩
  change (∃ z : ℤ, (Projective.Numerics.Construction.projectiveHilbertPolynomial (ClosedHilbertNumerics.Construction.coherentClosedDirectImage f M) j).eval (n : ℚ) = z)
  rw [← hb n hn]
  unfold Projective.Numerics.Construction.projectiveHilbertFunction
  exact ⟨_, (Int.cast_natCast _).symm⟩

theorem lineBundleHilbertPolynomial_eventually_integer (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∃ z : ℤ, (EffectiveHilbertDifference.Construction.lineBundleHilbertPolynomial f L j).eval (n : ℚ) = z := by
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have : L.sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation L
  exact closedProjectiveHilbertPolynomial_eventually_integer f L.sheaf j

theorem lineBundleHilbertDifference_eventually_integer (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∃ z : ℤ, (EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f L j).eval (n : ℚ) = z := by
  obtain ⟨b, hb⟩ := lineBundleHilbertPolynomial_eventually_integer f L j
  obtain ⟨c, hc⟩ := lineBundleHilbertPolynomial_eventually_integer f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X) j
  refine ⟨max b c, fun n hn => ?_⟩
  obtain ⟨a, ha⟩ := hb n ((le_max_left _ _).trans hn)
  obtain ⟨d, hd⟩ := hc n ((le_max_right _ _).trans hn)
  exact ⟨a - d, by rw [EffectiveHilbertDifference.Construction.lineBundleHilbertDifference, eval_sub, ha, hd, Int.cast_sub]⟩

variable [IsIntegral X]

theorem lineBundleHilbertCoefficient_nonneg_of_generated
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : Frame.SectionDetection.Construction.HasFrameSections L.sheaf) (j : Fin (r + 1)) (d : ℕ)
    (hd : (EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f L j).natDegree ≤ d) :
    0 ≤ LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient f L j d := by
  by_cases ht : Nonempty (L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
  · obtain ⟨e⟩ := ht
    change 0 ≤ (EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f L j).coeff d
    rw [EffectiveHilbertDifference.Construction.lineBundleHilbertDifference_eq_zero_of_trivial f L j e, coeff_zero]
  · change 0 ≤ (EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f L j).coeff d
    rcases lt_or_eq_of_le hd with hd | hd
    · rw [coeff_eq_zero_of_natDegree_lt hd]
    · rw [← hd, coeff_natDegree]
      exact (EffectiveHilbertDifference.Construction.lineBundleHilbertDifference_leadingCoeff_pos f L j hL ht).le

theorem lineBundleNumericalDegree_nonneg_of_generated
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : Frame.SectionDetection.Construction.HasFrameSections L.sheaf) (j : Fin (r + 1)) :
    0 ≤ PicardNumericalDegree.Construction.lineBundleNumericalDegree f L j :=
  lineBundleHilbertCoefficient_nonneg_of_generated f L hL j _
    (PicardNumericalDegree.Construction.lineBundleHilbertDifference_natDegree_le f L j)

theorem lineBundleNumericalDegree_factorial_integral (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) :
    ∃ z : ℤ,
      (((EffectiveHilbertDifference.Construction.lineBundleHilbertPolynomial f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X) j).natDegree - 1).factorial : ℚ) *
        PicardNumericalDegree.Construction.lineBundleNumericalDegree f L j = z := by
  obtain ⟨b, hb⟩ := lineBundleHilbertDifference_eventually_integer f L j
  exact PolynomialDifference.Construction.polynomial_factorial_coeff_integral_of_eventual_integer_values _ _
    (PicardNumericalDegree.Construction.lineBundleHilbertDifference_natDegree_le f L j) b hb

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.NumericalDegreeProperties
