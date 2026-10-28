import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationImage
import OAI.AlgebraicGeometry.Divisors.LineBundles.ProductPeriodicComplex
import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.Submodule
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Periodic Complex -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.PeriodicComplex.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the product complex on an actual local branch image

The augmentation is induced by the original quotient's map to its
localization. The branch module is finite over R, and denominators at
the prime satisfy the injectivity needed by the periodic scaling formula.
-/

variable {R : Type*} [CommRing R]

abbrev productBranchModule (a b : R) (P : Ideal R) [P.IsPrime] :=
  LocalizationImage.BundleCycles.localizationImage P.primeCompl (ProductPeriodicComplex.BundleCycles.productEquationQuotient a b)

def productBranchPeriodicComplex (a b : R) (P : Ideal R) [P.IsPrime] :
    HomologicalComplex (ModuleCat R) Periodic.PeriodicComplex.BundleCycles.periodicComplexShape :=
  Periodic.PeriodicComplex.BundleCycles.endomorphismPeriodicComplex
    (MultiplicationSequence.BundleCycles.equationEndomorphism a (productBranchModule a b P))
    (MultiplicationSequence.BundleCycles.equationEndomorphism b (productBranchModule a b P))
    (LocalizationImage.BundleCycles.localizationImage_equation_comp_zero P.primeCompl a b (ProductPeriodicComplex.BundleCycles.productEquation_comp_zero a b))
    (LocalizationImage.BundleCycles.localizationImage_equation_comp_zero P.primeCompl b a (ProductPeriodicComplex.BundleCycles.productEquation_comp_zero_reverse a b))

def productBranchAugmentation (a b : R) (P : Ideal R) [P.IsPrime] :
    ProductPeriodicComplex.BundleCycles.productPeriodicComplex a b ⟶ productBranchPeriodicComplex a b P :=
  Periodic.Submodule.BundleCycles.endomorphismPeriodicMap _ _ _ _ _ _ _ _ (LocalizationImage.BundleCycles.localizationImageProjection P.primeCompl)
    (by
      apply LinearMap.ext
      intro x
      exact ((LocalizationImage.BundleCycles.localizationImageProjection P.primeCompl).map_smul a x).symm)
    (by
      apply LinearMap.ext
      intro x
      exact ((LocalizationImage.BundleCycles.localizationImageProjection P.primeCompl).map_smul b x).symm)

theorem productBranchAugmentation_surjective (a b : R) (P : Ideal R) [P.IsPrime] (i : Bool) :
    Function.Surjective ((productBranchAugmentation a b P).f i) :=
  LocalizationImage.BundleCycles.localizationImageProjection_surjective P.primeCompl

theorem productBranch_denominator_injective (a b : R) (P : Ideal R) [P.IsPrime]
    (x : R) (hx : x ∉ P) :
    Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism x (productBranchModule a b P)) :=
  LocalizationImage.BundleCycles.localizationImage_equation_injective P.primeCompl ⟨x, hx⟩

def productBranchLocalEquiv (a b : R) (P : Ideal R) [P.IsPrime] :
    LocalizedModule P.primeCompl (productBranchModule a b P) ≃ₗ[R]
      LocalizedModule P.primeCompl (ProductPeriodicComplex.BundleCycles.productEquationQuotient a b) :=
  LocalizationImage.BundleCycles.localizationImageLocalEquiv P.primeCompl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.PeriodicComplex.BundleCycles
