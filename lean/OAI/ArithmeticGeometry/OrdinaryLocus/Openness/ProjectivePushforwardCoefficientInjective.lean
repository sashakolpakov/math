import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveFilteredSections

/-! # Projective Pushforward Coefficient Injective -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectivePushforwardCoefficientInjective.Construction

noncomputable section

/-! Normalized coefficients of an integral scheme's projective pushforward detect global sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

universe u

local instance projectivePushforwardCoefficientInjectiveMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

omit [Fintype σ] [LinearOrder σ] in
theorem projectivePushforwardCoefficientLinear_injective {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ)
    [Nonempty (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)] :
    Function.Injective (BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ
      ((Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X))
      (ProjectiveNormalizedSections.Construction.projectiveTwistUnitSection j n) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)) := by
  intro x y hxy
  apply ProjectiveFilteredSections.Construction.closedProjectiveNormalizedSectionMap_injective f j n
  exact congrArg (PushforwardOpenSections.Construction.pushforwardUnitOpenSectionsLinearEquiv f AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)) hxy

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectivePushforwardCoefficientInjective.Construction
