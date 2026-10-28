import OAI.RepresentationTheory.Weil.AdelicSplitting.Integral

/-! # Integral Local Coefficients -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntegralLocalCoefficients.CM

noncomputable section

/-! ThetaCycle: globally integral real-field coefficients belong to the actual
integer ring at every finite completion, including all exceptional places. -/

open IsDedekindDomain
open scoped _root_.NumberField
open OAI.RepresentationTheory.Weil.AdelicSplitting.Integral.Construction

theorem integral_scalar_at_every_finite_place (F : Type) [Field F] [NumberField F]
    (x : F) (hx : IsIntegral ℤ x) (v : HeightOneSpectrum (𝓞 F)) :
    RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) x ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) := by
  let y : 𝓞 F := ⟨x, hx⟩
  exact HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) v y

theorem integral_quadratic_at_every_finite_place (F : Type) [Field F] [NumberField F]
    (d : F) (x : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) (hr : IsIntegral ℤ x.re) (hi : IsIntegral ℤ x.im)
    (v : HeightOneSpectrum (𝓞 F)) :
    RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d (.inr v) x ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v) :=
  RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.quadraticOrder_of_coeff F d (.inr v) _
    (integral_scalar_at_every_finite_place F x.re hr v)
    (integral_scalar_at_every_finite_place F x.im hi v)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntegralLocalCoefficients.CM
