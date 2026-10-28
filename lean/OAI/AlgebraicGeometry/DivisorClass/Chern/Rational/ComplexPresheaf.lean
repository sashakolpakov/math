import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexCochains
import OAI.AlgebraicGeometry.DivisorClass.Chern.ModuleSheafificationForget
import OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf

/-! # Complex Presheaf -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexPresheaf

noncomputable section

/-! The original rational coefficient inclusion on actual presheaves of singular cochains. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def rationalToComplexAbelianCochainMap (X : TopCat.{0}) :
    (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.mapHomologicalComplex (.up ℕ)).obj (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) ⟶
      (Complex.SheafForget.complexModuleForget.mapHomologicalComplex (.up ℕ)).obj (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X) :=
  (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.mapHomologicalComplex (.up ℕ)).map (ComplexCochains.rationalToComplexCochainMap X)

def rationalComplexPresheafMap (X : TopCat.{0}) :
    ModuleSheafificationForget.moduleForgetPresheafComplex ℚ X (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) ⟶
      ModuleSheafificationForget.moduleForgetPresheafComplex ℂ X (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℂ ℂ) X) where
  f n := {
    app U := (rationalToComplexAbelianCochainMap (TopCat.of U.unop)).f n
    naturality U V i := by
      exact congrArg (fun g => AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.map (g.f n))
        (ComplexCochains.rationalToComplexCochainMap_naturality ((Opens.toTopCat X).map i.unop)) }
  comm' i j _ := by
    apply NatTrans.ext
    funext U
    exact (rationalToComplexAbelianCochainMap (TopCat.of U.unop)).comm i j

theorem rationalComplexPresheafMap_f_app (X : TopCat.{0}) (n : ℕ) (U : Opens X) :
    ((rationalComplexPresheafMap X).f n).app (op U) =
      AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.map ((ComplexCochains.rationalToComplexCochainMap (TopCat.of U)).f n) := rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexPresheaf
