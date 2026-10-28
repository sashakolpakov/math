import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ZeroForms
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Low Degree Flat -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.LowDegreeFlat.IntegralLowDegreeFlat

noncomputable section

/-! The first two native form modules are flat over a flat formally smooth base algebra. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Module.Flat R A] [Algebra.FormallySmooth R A]

theorem flat (n : ℕ) (hn : n ≤ 1) : Module.Flat R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · exact Module.Flat.of_linearEquiv ((ZeroForms.IntegralZeroForms.equiv R A).restrictScalars R)
  · let : Module.Flat R (KaehlerDifferential R A) := Module.Flat.trans R A _
    exact Module.Flat.of_linearEquiv ((OneForms.IntegralOneForms.equiv R A).restrictScalars R)

theorem regular (n : ℕ) (hn : n ≤ 1) (r : R) (hr : IsRegular r) :
    IsSMulRegular (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) r := by
  let := flat R A n hn
  exact Module.Flat.isSMulRegular_of_isRegular hr

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.LowDegreeFlat.IntegralLowDegreeFlat
