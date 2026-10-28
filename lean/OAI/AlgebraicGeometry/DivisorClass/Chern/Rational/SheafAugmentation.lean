import OAI.AlgebraicGeometry.DivisorClass.Chern.ThomSourceOrientation
import OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CupUnit

/-! # Sheaf Augmentation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SheafAugmentation

noncomputable section

/-! The canonical rational source augmentation is actual point evaluation followed by sheafification. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable (X : TopCat.{0})

def locallyConstantRationalSheafAugmentation :
    ConstantSheaf.RationalCech.locallyConstantRationalSheaf X ⟶
      (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)).X 0 :=
  (sheafificationIso (ConstantSheaf.RationalCech.locallyConstantRationalSheaf X)).hom ≫
    (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).map
      (Cech.Obj.RationalCech.locallyConstantSingularAugmentation X)

theorem locallyConstantRationalSheafAugmentation_hom :
    (locallyConstantRationalSheafAugmentation X).hom =
      Cech.Obj.RationalCech.locallyConstantSingularAugmentation X ≫
        CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X 0) :=
  (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X)
    (Cech.Obj.RationalCech.locallyConstantSingularAugmentation X)).symm

theorem locallyConstantRationalSheafAugmentation_one (U : Opens X) :
    (locallyConstantRationalSheafAugmentation X).hom.app (op U)
      (1 : LocallyConstant U ℚ) =
    (AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U).f 0
      (AlgebraicTopology.Products.Cup.singularCupUnit (R := ℚ) (TopCat.of U)) := by
  rw [locallyConstantRationalSheafAugmentation_hom]
  change (AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U).f 0
    (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) (TopCat.of U) (1 : LocallyConstant U ℚ)) = _
  rw [Relative.CupUnit.rationalPointAugmentation_one]

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SheafAugmentation
