import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ZeroForms
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.TwoForms
import OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectiveExterior
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Three Flat -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeFlat.IntegralFirstThreeFlat

noncomputable section

/-! The first three native form modules are flat over a flat formally smooth base algebra. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Module.Flat R A] [Algebra.FormallySmooth R A]

theorem flat (n : ℕ) (hn : n ≤ 2) : Module.Flat R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) := by
  rcases n with _ | (_ | (_ | n))
  · exact Module.Flat.of_linearEquiv ((Integral.ZeroForms.IntegralZeroForms.equiv R A).restrictScalars R)
  · let : Module.Flat R (KaehlerDifferential R A) := Module.Flat.trans R A _
    exact Module.Flat.of_linearEquiv ((Integral.OneForms.IntegralOneForms.equiv R A).restrictScalars R)
  · let : Module.Projective A (⋀[A]^2 (KaehlerDifferential R A)) :=
      ProjectiveExterior.ProjectiveExteriorPower.projective A (KaehlerDifferential R A) 2
    let : Module.Flat R (⋀[A]^2 (KaehlerDifferential R A)) := Module.Flat.trans R A _
    exact Module.Flat.of_linearEquiv ((Integral.TwoForms.IntegralTwoForms.equiv R A).restrictScalars R)
  · omega

theorem regular (n : ℕ) (hn : n ≤ 2) (r : R) (hr : IsRegular r) :
    IsSMulRegular (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) r := by
  let := flat R A n hn
  exact Module.Flat.isSMulRegular_of_isRegular hr

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeFlat.IntegralFirstThreeFlat
