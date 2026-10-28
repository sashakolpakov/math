import OAI.AlgebraicTopology.Cohomology.Singular.RationalComplex

/-! # Complex Cochains -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexCochains

noncomputable section

/-! The original rational-to-complex cohomology inclusion comes from this actual cochain map. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.RationalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def rationalRestrictedComplexInclusion :
    ModuleCat.of ℚ ℚ ⟶ (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj (ModuleCat.of ℂ ℂ) :=
  ModuleCat.ofHom AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion ≫ AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.hom

def rationalToComplexCochainMap (X : TopCat.{0}) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X ⟶
      ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex (.up ℕ)).obj
        (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X) :=
  AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap rationalRestrictedComplexInclusion X ≫
    (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X).inv

theorem rationalToComplexCochainMap_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f ≫ rationalToComplexCochainMap X =
      rationalToComplexCochainMap Y ≫
        ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex (.up ℕ)).map
          (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f) := by
  let eX := AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X
  let eY := AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) Y
  have hi : AlgebraicTopology.Cohomology.Singular.Functor.singularPullback ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj (ModuleCat.of ℂ ℂ)) f ≫ eX.inv =
      eY.inv ≫ ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex (.up ℕ)).map
        (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f) := by
    apply eY.eq_inv_comp.mpr
    rw [← Category.assoc, ← AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold rationalToComplexCochainMap
  rw [← Category.assoc, AlgebraicTopology.Cohomology.Singular.Functor.coefficientCochainMap_naturality, Category.assoc, hi, ← Category.assoc]

theorem rationalToComplexCochainMap_homology (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (rationalToComplexCochainMap X) n ≫
      (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X).sc n).mapHomologyIso
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).hom = AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X n := by
  unfold rationalToComplexCochainMap rationalRestrictedComplexInclusion
  rw [AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap_comp]
  simp only [HomologicalComplex.homologyMap_comp, Category.assoc]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexCochains
