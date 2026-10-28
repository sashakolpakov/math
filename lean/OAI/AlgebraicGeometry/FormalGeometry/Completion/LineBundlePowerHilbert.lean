import OAI.AlgebraicGeometry.FormalGeometry.Completion.LineBundleHilbertCoefficients
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPowersAdd

/-! # Line Bundle Power Hilbert -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.LineBundlePowerHilbert

noncomputable section

/-! Positive tensor powers preserve the degree of a generated line bundle's
Hilbert difference and multiply its leading coefficient by the exponent. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Polynomial

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] [Infinite K] {r : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)) [IsClosedImmersion f]

theorem lineBundleHilbertCoefficient_tensorPower (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (hL : Frame.SectionDetection.Construction.HasFrameSections L.sheaf) (j : Fin (r + 1)) (d : ℕ)
    (hd : (EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f L j).natDegree ≤ d) (n : ℕ) :
    LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient f (L.tensorPower n) j d =
      (n : ℚ) * LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient f L j d := by
  induction n with
  | zero =>
    obtain ⟨e⟩ := Quotient.exact (Quotients.FiniteDescent.PicardPowersAdd.Construction.PicardPowers.class_zero L)
    have hz := EffectiveHilbertDifference.Construction.lineBundleHilbertDifference_eq_zero_of_trivial f (L.tensorPower 0) j e
    unfold LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient
    rw [hz, coeff_zero, Nat.cast_zero, zero_mul]
  | succ n ih =>
    have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower (n + 1)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensor (L.tensorPower n)) := by
      change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower (n + 1)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L * AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower n)
      rw [Quotients.FiniteDescent.PicardPowersAdd.Construction.PicardPowers.class_pow, Quotients.FiniteDescent.PicardPowersAdd.Construction.PicardPowers.class_pow, pow_succ']
    obtain ⟨e⟩ := Quotient.exact hc
    rw [LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient_iso f _ _ e j d,
      LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient_tensor_generated_left f L (L.tensorPower n) hL j d hd, ih]
    push_cast
    ring

theorem lineBundleHilbertDifference_tensorPower_natDegree_le (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (hL : Frame.SectionDetection.Construction.HasFrameSections L.sheaf) (j : Fin (r + 1)) (n : ℕ) :
    (EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f (L.tensorPower n) j).natDegree ≤
      (EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f L j).natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  change LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient f (L.tensorPower n) j i = 0
  rw [lineBundleHilbertCoefficient_tensorPower f L hL j i hi.le]
  unfold LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient
  rw [coeff_eq_zero_of_natDegree_lt hi, mul_zero]

theorem lineBundleHilbertDifference_tensorPower_leading (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (hL : Frame.SectionDetection.Construction.HasFrameSections L.sheaf) (j : Fin (r + 1)) (n : ℕ) (hn : 0 < n) :
    (EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f (L.tensorPower n) j).natDegree =
        (EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f L j).natDegree ∧
      (EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f (L.tensorPower n) j).leadingCoeff =
        (n : ℚ) * (EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f L j).leadingCoeff := by
  let P := EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f L j
  let Q := EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f (L.tensorPower n) j
  have hd : Q.natDegree ≤ P.natDegree := lineBundleHilbertDifference_tensorPower_natDegree_le f L hL j n
  have hc : Q.coeff P.natDegree = (n : ℚ) * P.leadingCoeff := by
    simpa only [LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient, P, Q, coeff_natDegree] using
      lineBundleHilbertCoefficient_tensorPower f L hL j P.natDegree le_rfl n
  by_cases hP : P = 0
  · have hQ : Q = 0 := by
      apply Polynomial.ext
      intro i
      change LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient f (L.tensorPower n) j i = (0 : Polynomial ℚ).coeff i
      rw [lineBundleHilbertCoefficient_tensorPower f L hL j i (by change P.natDegree ≤ i; simp [hP])]
      change (n : ℚ) * P.coeff i = _
      simp [hP]
    change Q.natDegree = P.natDegree ∧ Q.leadingCoeff = (n : ℚ) * P.leadingCoeff
    simp [hP, hQ]
  · have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have hcne : Q.coeff P.natDegree ≠ 0 := by
      rw [hc]
      exact mul_ne_zero hnq (leadingCoeff_ne_zero.mpr hP)
    have he : Q.natDegree = P.natDegree := le_antisymm hd (le_natDegree_of_ne_zero hcne)
    refine ⟨he, ?_⟩
    change Q.leadingCoeff = (n : ℚ) * P.leadingCoeff
    rw [← coeff_natDegree, he, hc]

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.LineBundlePowerHilbert
