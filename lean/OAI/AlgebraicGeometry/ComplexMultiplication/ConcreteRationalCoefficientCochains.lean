import OAI.AlgebraicTopology.Cohomology.Singular.RationalComplex

/-! # Concrete Rational Coefficient Cochains -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ConcreteRationalCoefficientCochains

noncomputable section

/-! # Actual rational-to-complex coefficients on genuine singular cochains

Scalar restriction retains evaluation on every continuous singular simplex.
The cochain map below induces the existing rational-to-complex cohomology map.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

open OAI.AlgebraicTopology.Cohomology.Singular.RationalComplex

set_option backward.isDefEq.respectTransparency false in
/-- Restricting scalars leaves the value on each actual singular simplex unchanged. -/
theorem singularCochainsRestriction_hom_evaluation
    {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{0} S) (Y : TopCat.{0}) {n : ℕ} (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices Y n) :
    (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso f M Y).hom.f n ≫
        AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj Y)
          ((ModuleCat.restrictScalars f).obj M) s =
      (ModuleCat.restrictScalars f).map
        (AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj Y) M s) := by
  exact congrArg Quiver.Hom.unop
    (ι_comp_sigmaComparison (ModuleCat.restrictScalars f).op
      (fun _ : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices Y n => op M) s)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse restriction comparison also retains each simplex value. -/
theorem singularCochainsRestriction_inv_evaluation
    {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{0} S) (Y : TopCat.{0}) {n : ℕ} (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices Y n) :
    (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso f M Y).inv.f n ≫
        (ModuleCat.restrictScalars f).map
          (AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj Y) M s) =
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj Y)
        ((ModuleCat.restrictScalars f).obj M) s := by
  rw [← singularCochainsRestriction_hom_evaluation f M Y s, ← Category.assoc]
  have h := congrArg (fun k => k.f n)
    (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso f M Y).inv_hom_id
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at h
  rw [h, Category.id_comp]

/-- The literal coefficient inclusion, followed by the actual scalar-restriction comparison. -/
def actualRationalToComplexCochainMap (Y : TopCat.{0}) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) Y ⟶
      ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) Y) :=
  AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap (ModuleCat.ofHom AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion) Y ≫
    AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.hom Y ≫
      (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) Y).inv

set_option backward.isDefEq.respectTransparency false in
/-- This coefficient inclusion casts the rational value on every simplex into ℂ. -/
theorem actualRationalToComplexCochainMap_evaluation (Y : TopCat.{0})
    {n : ℕ} (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices Y n) :
    (actualRationalToComplexCochainMap Y).f n ≫
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map
          (AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj Y) (ModuleCat.of ℂ ℂ) s) =
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ) s ≫
        ModuleCat.ofHom AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion ≫ AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.hom := by
  simp only [actualRationalToComplexCochainMap, HomologicalComplex.comp_f, Category.assoc]
  rw [singularCochainsRestriction_inv_evaluation]
  rw [AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap_evaluation,
    ← Category.assoc, AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap_evaluation]
  exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The induced cohomology map is the existing ordinary rational-to-complex map. -/
theorem actualRationalToComplexCochainMap_homology (Y : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (actualRationalToComplexCochainMap Y) n ≫
        (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) Y).sc n).mapHomologyIso
          (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).hom =
      AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology Y n := by
  simp only [actualRationalToComplexCochainMap, HomologicalComplex.homologyMap_comp,
    AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology, AlgebraicTopology.Cohomology.Singular.RationalInjection.rationalComplexCoefficientMap, AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap,
    AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso, AlgebraicTopology.Cohomology.Singular.Chains.singularCohomologyRestrictScalarsIso,
    Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ConcreteRationalCoefficientCochains
