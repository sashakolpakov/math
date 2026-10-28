import OAI.AlgebraicGeometry.ComplexMultiplication.SingularPresheafBridge
import OAI.AlgebraicTopology.Cohomology.Singular.Augmentation
import OAI.AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant

/-! # Singular Presheaf Constants -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SingularPresheafConstants

noncomputable section

/-! # Actual singular evaluation preserves constant zero-cochains

The constant augmentation is checked on genuine simplex chains, so its value
and normalization are retained by the original presheaf comparison.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped Simplicial

/-- The original zero-chain augmentation has value one on every actual vertex chain. -/
theorem originalZeroAugmentation_simplex (R : Type) [CommRing R] (S : SSet.{0})
    (s : S _⦋0⦌) :
    (AlgebraicTopology.Singular.SheafCochain.simplicialZeroAugmentation R S).hom
        (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain S s) = 1 :=
  congrArg (fun f ↦ f.hom 1)
    (AlgebraicTopology.Singular.SheafCochain.ιChainComplex_comp_simplicialZeroAugmentation R S s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Chain evaluation retains the exact original constant-presheaf augmentation. -/
theorem singularPresheafBridge_constant (Y : TopCat.{0}) :
    _root_.CategoryTheory.Functor.whiskerRight
        (AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantToLocallyConstant Y ≫
          AlgebraicTopology.Cohomology.Singular.Augmentation.Comparison.locallyConstantSingularAugmentation Y)
        (forget₂ (ModuleCat ℂ) AddCommGrpCat) ≫
      (SingularPresheafBridge.singularCochainDegreePresheafBridgeIso ℂ Y 0).hom =
        AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZero ℂ Y := by
  apply _root_.CategoryTheory.NatTrans.ext
  funext U
  rw [NatTrans.comp_app, SingularPresheafBridge.singularCochainDegreePresheafBridgeIso_hom_app]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  change ℂ at c
  change AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv
      (TopCat.toSSet.obj (TopCat.of U.unop)) (ModuleCat.of ℂ ℂ) 0
      ((AlgebraicTopology.Cohomology.Singular.Augmentation.Comparison.locallyConstantSingularAugmentation Y).app U
        ((AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantToLocallyConstant Y).app U c)) =
    c • (AlgebraicTopology.Singular.SheafCochain.openZeroAugmentation ℂ Y U).hom
  apply AlgebraicTopology.Cohomology.Singular.ChainDual.chainFunctional_ext
    (TopCat.toSSet.obj (TopCat.of U.unop)) (ModuleCat.of ℂ ℂ)
  intro s
  rw [AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex]
  rw [← AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply,
    ← AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_apply_simplex,
    AlgebraicTopology.Cohomology.Singular.Augmentation.Comparison.locallyConstantSingularAugmentation_apply]
  change c = c * (AlgebraicTopology.Singular.SheafCochain.simplicialZeroAugmentation ℂ
    (TopCat.toSSet.obj (TopCat.of U.unop))).hom
      (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (TopCat.toSSet.obj (TopCat.of U.unop)) s)
  rw [originalZeroAugmentation_simplex, mul_one]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SingularPresheafConstants
