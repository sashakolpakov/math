import OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredSections

/-! # Pushforward Coefficient Injective -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PushforwardCoefficientInjective.Dimension

noncomputable section

/-! Normalized coefficients of an integral scheme's projective pushforward detect global sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

universe u

local instance projectivePushforwardCoefficientInjectiveMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

omit [Fintype σ] [LinearOrder σ] in
theorem projectivePushforwardCoefficientLinear_injective {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ)
    [Nonempty (f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)] :
    Function.Injective (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear MvPolynomialClosure.MvPolynomial.homogeneousProjπ
      ((Scheme.Modules.pushforward f).obj (Invertible.Scheme.Modules.unitObj X))
      (UnitSection.Dimension.projectiveTwistUnitSection j n) (MvPolynomialClosure.MvPolynomial.coordinateOpen j)) := by
  intro x y hxy
  apply FilteredSections.Dimension.closedProjectiveNormalizedSectionMap_injective f j n
  exact congrArg (ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardOpenSections.Construction.pushforwardUnitOpenSectionsLinearEquiv f MvPolynomialClosure.MvPolynomial.homogeneousProjπ (MvPolynomialClosure.MvPolynomial.coordinateOpen j)) hxy

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PushforwardCoefficientInjective.Dimension
