import OAI.AlgebraicTopology.Cohomology.Singular.RationalInjection
import OAI.AlgebraicTopology.Cohomology.Singular.Chains
import OAI.AlgebraicTopology.Cohomology.Singular.Functor

/-! # Rational Complex -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.RationalComplex

noncomputable section

/-!
# Rational classes inside ordinary complex singular cohomology

The rational-to-complex coefficient map lands in the usual singular cohomology
computed in complex modules, after restricting that cohomology's scalars to the
rationals. The restriction comparison is induced by the actual cochain complex.
The rational-linear coefficient retraction proves injectivity for every space.
-/

open _root_.CategoryTheory

/-- The usual rational module of complex numbers agrees with restriction of the
usual complex coefficient module. Both directions are the identity on values. -/
def complexCoefficientsRestrictionIso :
    ModuleCat.of ℚ ℂ ≅
      (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj (ModuleCat.of ℂ ℂ) where
  hom := ModuleCat.ofHom
    { toFun := fun z => z
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro q z
        change q • z = (algebraMap ℚ ℂ q) * z
        exact Algebra.smul_def q z }
  inv := ModuleCat.ofHom
    { toFun := fun z => z
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro q z
        change (algebraMap ℚ ℂ q) * z = q • z
        exact (Algebra.smul_def q z).symm }
  hom_inv_id := by ext z; rfl
  inv_hom_id := by ext z; rfl

@[simp]
theorem complexCoefficientsRestrictionIso_hom_apply (z : ℂ) :
    complexCoefficientsRestrictionIso.hom z = z := rfl

@[simp]
theorem complexCoefficientsRestrictionIso_inv_apply (z : ℂ) :
    complexCoefficientsRestrictionIso.inv z = z := rfl

/-- Ordinary complex singular cohomology, regarded as a rational module. -/
abbrev complexCohomologyAsRational (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} ℚ :=
  (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj
    (Basic.singularCohomology (ModuleCat.of ℂ ℂ) X n)

/-- Computing complex-valued cohomology in rational modules or computing it in
complex modules and restricting scalars gives the same rational module. -/
def complexCohomologyRestrictionIso (X : TopCat.{0}) (n : ℕ) :
    Basic.singularCohomology (ModuleCat.of ℚ ℂ) X n ≅ complexCohomologyAsRational X n :=
  (Coefficients.coefficientFunctor X n).mapIso complexCoefficientsRestrictionIso ≪≫
    Chains.singularCohomologyRestrictScalarsIso (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X n

/-- The usual inclusion of rational singular classes into ordinary complex
singular cohomology, with the target regarded as a rational module. -/
def rationalToComplexCohomology (X : TopCat.{0}) (n : ℕ) :
    Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n ⟶ complexCohomologyAsRational X n :=
  RationalInjection.rationalComplexCoefficientMap X n ≫ (complexCohomologyRestrictionIso X n).hom

/-- A rational-linear left inverse for the coefficient inclusion on ordinary
complex cohomology. This retraction is not asserted to be complex-linear. -/
def complexToRationalCohomology (X : TopCat.{0}) (n : ℕ) :
    complexCohomologyAsRational X n ⟶ Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n :=
  (complexCohomologyRestrictionIso X n).inv ≫ RationalInjection.complexRationalCoefficientMap X n

@[simp]
theorem rationalToComplexCohomology_comp_retraction (X : TopCat.{0}) (n : ℕ) :
    rationalToComplexCohomology X n ≫ complexToRationalCohomology X n =
      𝟙 (Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n) := by
  simp [rationalToComplexCohomology, complexToRationalCohomology, Category.assoc]

/-- Rational singular cohomology injects into ordinary complex singular
cohomology in every degree, without a finiteness hypothesis on the space. -/
theorem rationalToComplexCohomology_injective (X : TopCat.{0}) (n : ℕ) :
    Function.Injective (rationalToComplexCohomology X n) :=
  (complexCohomologyRestrictionIso X n).toLinearEquiv.injective.comp
    (RationalInjection.rationalComplexCoefficientMap_injective X n)

/-- The complex-coefficient comparison commutes with pullback in the space. -/
theorem complexCohomologyRestrictionIso_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) :
    Functor.singularCohomologyPullback (ModuleCat.of ℚ ℂ) f n ≫
        (complexCohomologyRestrictionIso X n).hom =
      (complexCohomologyRestrictionIso Y n).hom ≫
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map
          (Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) f n) := by
  change Functor.singularCohomologyPullback (ModuleCat.of ℚ ℂ) f n ≫
      (Coefficients.coefficientMap complexCoefficientsRestrictionIso.hom X n ≫
        (Chains.singularCohomologyRestrictScalarsIso (algebraMap ℚ ℂ)
          (ModuleCat.of ℂ ℂ) X n).hom) =
    (Coefficients.coefficientMap complexCoefficientsRestrictionIso.hom Y n ≫
        (Chains.singularCohomologyRestrictScalarsIso (algebraMap ℚ ℂ)
          (ModuleCat.of ℂ ℂ) Y n).hom) ≫ _
  rw [← Category.assoc, Functor.coefficientMap_naturality, Category.assoc,
    Chains.singularCohomologyRestrictScalarsIso_naturality]
  exact (Category.assoc _ _ _).symm

/-- The ordinary rational-to-complex inclusion commutes with pullback. -/
theorem rationalToComplexCohomology_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) :
    Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f n ≫
        rationalToComplexCohomology X n =
      rationalToComplexCohomology Y n ≫
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map
          (Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) f n) := by
  change Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f n ≫
      (Coefficients.coefficientMap (ModuleCat.ofHom RationalRetraction.rationalInclusion) X n ≫
        (complexCohomologyRestrictionIso X n).hom) =
    (Coefficients.coefficientMap (ModuleCat.ofHom RationalRetraction.rationalInclusion) Y n ≫
      (complexCohomologyRestrictionIso Y n).hom) ≫ _
  rw [← Category.assoc, Functor.coefficientMap_naturality, Category.assoc,
    complexCohomologyRestrictionIso_naturality]
  exact (Category.assoc _ _ _).symm

end

end OAI.AlgebraicTopology.Cohomology.Singular.RationalComplex
