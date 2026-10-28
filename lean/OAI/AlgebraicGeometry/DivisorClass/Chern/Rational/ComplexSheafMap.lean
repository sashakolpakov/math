import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexPresheaf
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.BettiSheafComparison
import OAI.AlgebraicTopology.Cohomology.Singular.SheafResolution

/-! # Complex Sheaf Map -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexSheafMap

noncomputable section

/-! The actual rational-to-complex coefficient map on singular sheaves and its sheafification units. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.Cohomology.Singular.SheafResolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0})

def complexAbelianSingularResolution := Complex.SheafForget.complexSheafForgetComplex (AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex X)

def rationalComplexSingularSheafMap :
    BettiSheafComparison.rationalAbelianSingularResolution X ⟶ complexAbelianSingularResolution X :=
  (ModuleSheafificationForget.moduleForgetSheafificationComplexIso ℚ X (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)).inv ≫
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℕ)).map
      (ComplexPresheaf.rationalComplexPresheafMap X) ≫
    (ModuleSheafificationForget.moduleForgetSheafificationComplexIso ℂ X (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℂ ℂ) X)).hom

theorem moduleForgetSheafificationIso_inv_unit (R : Type) [Ring R] (P : X.Presheaf (ModuleCat.{0} R)) :
    Functor.whiskerRight (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)
        (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}) ≫ (ModuleSheafificationForget.moduleForgetSheafificationIso R X P).inv.hom =
      CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (P ⋙ forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}) := by
  rw [← ModuleSheafificationForget.moduleForgetSheafificationIso_unit, Category.assoc]
  change _ ≫ ((ModuleSheafificationForget.moduleForgetSheafificationIso R X P).hom ≫ (ModuleSheafificationForget.moduleForgetSheafificationIso R X P).inv).hom = _
  rw [Iso.hom_inv_id]
  exact Category.comp_id _

theorem rationalComplexSingularSheafMap_unit (n : ℕ) :
    Functor.whiskerRight (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X n)) AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget ≫
      ((rationalComplexSingularSheafMap X).f n).hom =
    (ComplexPresheaf.rationalComplexPresheafMap X).f n ≫
      Functor.whiskerRight (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℂ ℂ) X).X n)) Complex.SheafForget.complexModuleForget := by
  change _ ≫ ((ModuleSheafificationForget.moduleForgetSheafificationIso ℚ X _).inv.hom ≫
    CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) ((ComplexPresheaf.rationalComplexPresheafMap X).f n) ≫
      (ModuleSheafificationForget.moduleForgetSheafificationIso ℂ X _).hom.hom) = _
  rw [← Category.assoc, moduleForgetSheafificationIso_inv_unit,
    ← Category.assoc, ← CategoryTheory.toSheafify_naturality, Category.assoc]
  exact congrArg (fun f => (ComplexPresheaf.rationalComplexPresheafMap X).f n ≫ f)
    (ModuleSheafificationForget.moduleForgetSheafificationIso_unit ℂ X ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℂ ℂ) X).X n))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexSheafMap
