import OAI.AlgebraicTopology.Cohomology.Singular.RationalRetraction
import OAI.AlgebraicTopology.Cohomology.Singular.SplitInjection

/-! # Rational Injection -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.RationalInjection

noncomputable section

/-!
# Injectivity of the rational-to-complex coefficient map

Here the complex coefficient module is regarded as a rational vector space.
The map on actual singular cohomology is induced by the usual inclusion of
rational numbers into complex numbers. A constructed rational-linear retraction
proves its injectivity for every topological space and every degree.

The comparison with singular cohomology formed in the category of complex
modules is supplied separately by restriction of scalars.
-/

open _root_.CategoryTheory

/-- The ordinary rational inclusion, regarded as a morphism of rational modules,
has the constructed rational-linear retraction. -/
theorem rationalCoefficient_split :
    (ModuleCat.ofHom RationalRetraction.rationalInclusion : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℂ) ≫
      ModuleCat.ofHom RationalRetraction.rationalRetraction = 𝟙 (ModuleCat.of ℚ ℚ) := by
  apply ModuleCat.hom_ext
  exact RationalRetraction.rationalRetraction_comp_inclusion

/-- Change from rational to complex-valued coefficients in singular cohomology,
with both coefficient modules regarded as rational vector spaces. -/
def rationalComplexCoefficientMap (X : TopCat.{0}) (n : ℕ) :
    Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n ⟶
      Basic.singularCohomology (ModuleCat.of ℚ ℂ) X n :=
  Coefficients.coefficientMap (ModuleCat.ofHom RationalRetraction.rationalInclusion) X n

/-- The cohomology map induced by the selected rational-linear retraction. -/
def complexRationalCoefficientMap (X : TopCat.{0}) (n : ℕ) :
    Basic.singularCohomology (ModuleCat.of ℚ ℂ) X n ⟶
      Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n :=
  Coefficients.coefficientMap (ModuleCat.ofHom RationalRetraction.rationalRetraction) X n

/-- The two induced coefficient maps compose to the identity. -/
@[simp]
theorem rationalComplexCoefficientMap_comp_retraction (X : TopCat.{0}) (n : ℕ) :
    rationalComplexCoefficientMap X n ≫ complexRationalCoefficientMap X n =
      𝟙 (Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n) := by
  change Coefficients.coefficientMap (ModuleCat.ofHom RationalRetraction.rationalInclusion) X n ≫
    Coefficients.coefficientMap (ModuleCat.ofHom RationalRetraction.rationalRetraction) X n = _
  rw [← Coefficients.coefficientMap_comp, rationalCoefficient_split, Coefficients.coefficientMap_id]

/-- The constructed retraction recovers each rational singular cohomology class. -/
theorem complexRationalCoefficientMap_leftInverse (X : TopCat.{0}) (n : ℕ) :
    Function.LeftInverse (complexRationalCoefficientMap X n)
      (rationalComplexCoefficientMap X n) :=
  SplitInjection.coefficientMap_leftInverse_of_split (ModuleCat.ofHom RationalRetraction.rationalInclusion)
    (ModuleCat.ofHom RationalRetraction.rationalRetraction) rationalCoefficient_split X n

/-- Rational singular cohomology injects under the usual change to complex-valued
coefficients, without a finite-dimensionality hypothesis. -/
theorem rationalComplexCoefficientMap_injective (X : TopCat.{0}) (n : ℕ) :
    Function.Injective (rationalComplexCoefficientMap X n) :=
  (complexRationalCoefficientMap_leftInverse X n).injective

/-- Two rational singular cohomology classes have equal complex coefficient images
exactly when they are equal. -/
theorem rationalComplexCoefficientMap_eq_iff (X : TopCat.{0}) (n : ℕ)
    (x y : Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n) :
    rationalComplexCoefficientMap X n x = rationalComplexCoefficientMap X n y ↔ x = y :=
  (rationalComplexCoefficientMap_injective X n).eq_iff

end

end OAI.AlgebraicTopology.Cohomology.Singular.RationalInjection
