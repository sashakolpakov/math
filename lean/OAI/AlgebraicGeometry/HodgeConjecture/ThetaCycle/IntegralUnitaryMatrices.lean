import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntegralLocalCoefficients
import OAI.RepresentationTheory.Theta.Adelic.RationalSU

/-! # Integral Unitary Matrices -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntegralUnitaryMatrices.CM

noncomputable section

/-! ThetaCycle: integral quadratic coefficients of a rational unitary matrix
and its inverse put its diagonal image in every local integral subgroup. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.IntegralTopology OAI.RepresentationTheory.Theta.Adelic.RationalSU

theorem quadratic_matrix_entry_integral_of_difference
    {F I : Type*} [Field F] [CharZero F] [Fintype I] [DecidableEq I]
    (d : F) (A : Matrix I I (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) (i j : I)
    (hr : IsIntegral ℤ (A i j - (1 : Matrix I I (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) i j).re)
    (hi : IsIntegral ℤ (A i j - (1 : Matrix I I (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) i j).im) :
    IsIntegral ℤ (A i j).re ∧ IsIntegral ℤ (A i j).im := by
  have ho : IsIntegral ℤ ((1 : Matrix I I (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) i j).re ∧
      IsIntegral ℤ ((1 : Matrix I I (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) i j).im := by
    by_cases hij : i = j
    · subst j
      simp only [Matrix.one_apply]
      change IsIntegral ℤ (1 : F) ∧ IsIntegral ℤ (0 : F)
      exact ⟨isIntegral_one, isIntegral_zero⟩
    · simp only [Matrix.one_apply, ite_eq_right hij]
      exact ⟨isIntegral_zero, isIntegral_zero⟩
  have he : A i j = (A i j - (1 : Matrix I I (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) i j) +
      (1 : Matrix I I (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) i j := (sub_add_cancel _ _).symm
  rw [he]
  exact ⟨hr.add ho.1, hi.add ho.2⟩

theorem local_rational_su_integral_of_coefficients
    (F : Type) [Field F] [NumberField F] {d : F} {n : ℕ}
    (H : (Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ) (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val)
    (hg : ∀ i j, IsIntegral ℤ (g.val.val i j).re ∧ IsIntegral ℤ (g.val.val i j).im)
    (hi : ∀ i j, IsIntegral ℤ ((g⁻¹).val.val i j).re ∧ IsIntegral ℤ ((g⁻¹).val.val i j).im)
    (v : HeightOneSpectrum (𝓞 F)) :
    RepresentationTheory.Theta.Adelic.RationalSU.rationalLocalSU F H (.inr v) g ∈ RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr v) := by
  constructor
  · intro i j
    exact IntegralLocalCoefficients.CM.integral_quadratic_at_every_finite_place F d (g.val.val i j) (hg i j).1 (hg i j).2 v
  · intro i j
    exact IntegralLocalCoefficients.CM.integral_quadratic_at_every_finite_place F d ((g⁻¹).val.val i j) (hi i j).1 (hi i j).2 v

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntegralUnitaryMatrices.CM
