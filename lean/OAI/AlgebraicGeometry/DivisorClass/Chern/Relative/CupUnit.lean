import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ConstantSheaf
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCup
import OAI.AlgebraicTopology.Products.Cup

/-! # Cup Unit -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CupUnit

noncomputable section

/-! Literal constant-one point evaluation is the unit of the original supported cup product. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCup.Cycles OAI.AlgebraicTopology.Products.Cup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem rationalPointAugmentation_one (X : TopCat.{0}) :
    AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) X (1 : LocallyConstant X ℚ) =
      AlgebraicTopology.Products.Cup.singularCupUnit (R := ℚ) X := by
  apply (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) X).toLinearEquiv.injective
  funext x
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) X).hom
      (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) X (1 : LocallyConstant X ℚ)) x =
    (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) X).hom (AlgebraicTopology.Products.Cup.singularCupUnit (R := ℚ) X) x
  rw [AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_apply, AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_apply,
    AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply]
  exact (AlgebraicTopology.Products.Cup.evaluation_cupUnit (R := ℚ) (TopCat.toSSet.obj X)
    (TopCat.toSSetObj₀Equiv.symm x)).symm

theorem relativeAbsoluteCup_unit (X : TopCat.{0}) (A : Set X) (p : ℕ)
    (a : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p) :
    CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X A p 0 a (AlgebraicTopology.Products.Cup.singularCupUnit (R := ℚ) X) = a := by
  apply CycleClass.Geometric.RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective (ModuleCat.of ℚ ℚ) X A p
  exact (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCupWith_inclusion X A (M := ModuleCat.of ℚ ℚ)
    (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ) (LinearMap.mul ℚ ℚ)
    a (AlgebraicTopology.Products.Cup.singularCupUnit (R := ℚ) X)).trans
      (AlgebraicTopology.Products.Cup.cup_cupUnit (TopCat.toSSet.obj X)
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p a))

theorem relativeAbsoluteCup_pointAugmentation_one (X : TopCat.{0}) (A : Set X) (p : ℕ)
    (a : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p) :
    CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X A p 0 a
      (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) X (1 : LocallyConstant X ℚ)) = a := by
  rw [rationalPointAugmentation_one, relativeAbsoluteCup_unit]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CupUnit
