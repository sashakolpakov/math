import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.TwoFormsEtale

/-! # Three Localization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeLocalization.IntegralFirstThreeLocalization

noncomputable section

/-! Localization of the actual form modules through degree two over arbitrary rings. -/

universe u

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem isLocalized (T : Submonoid A) [IsLocalization T B] (n : ℕ) (hn : n ≤ 2) :
    IsLocalizedModule T (Forms.CoordinateLinearity.FormsBaseChange.coordinateFormMap R A B n) := by
  by_cases h : n ≤ 1
  · exact Integral.LowDegreeLocalization.IntegralLowDegreeLocalization.isLocalized R A B T n h
  · have he : n = 2 := by omega
    subst n
    exact Integral.TwoFormsEtale.IntegralTwoFormsEtale.isLocalized R A B T

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeLocalization.IntegralFirstThreeLocalization
